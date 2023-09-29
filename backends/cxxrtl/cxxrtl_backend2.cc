/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019-2022  whitequark <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/mem.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/modtools.h"
#include "kernel/utils.h"
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::SyncType;

bool is_unary_cell(IdString type)
{
	return type.in(
		ID($not), ID($logic_not), ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
		ID($pos), ID($neg));
}

bool is_binary_cell(IdString type)
{
	return type.in(
		ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and), ID($logic_or),
		ID($shl), ID($sshl), ID($shr), ID($sshr), ID($shift), ID($shiftx),
		ID($eq), ID($ne), ID($eqx), ID($nex), ID($gt), ID($ge), ID($lt), ID($le),
		ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($modfloor));
}

// bool is_extending_cell(IdString type)
// {
// 	return !type.in(
// 		ID($logic_not), ID($logic_and), ID($logic_or),
// 		ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool));
// }

bool is_pure_cell(IdString type)
{
	return is_unary_cell(type) || is_binary_cell(type) || type.in(
		ID($mux), ID($concat), ID($slice), ID($pmux), ID($bmux), ID($demux));
}

// bool is_internal_cell(IdString type)
// {
// 	return !type.isPublic() && !type.begins_with("$paramod");
// }

struct CxxWriter {
	std::ostream *out = nullptr;
	std::vector<std::pair<std::stringstream, std::stringstream>> scopes;
	std::string level;

	void indent()
	{
		level += "\t";
	}

	void dedent()
	{
		level.resize(level.size() - 1);
	}

	void write(char c)
	{
		*out << c;
		if (c == '\n')
			*out << level;
	}

	void write(const std::string &s)
	{
		for (char c : s)
			write(c);
	}

	void writeln(const std::string &s = "")
	{
		write(s);
		write('\n');
	}
	
	std::stringstream& decl()
	{
		log_assert(!scopes.empty());
		return scopes.back().first;
	}

	std::stringstream& body()
	{
		log_assert(!scopes.empty());
		return scopes.back().second;
	}

	void push()
	{
		indent();
		
		scopes.push_back({});
	}
	
	void pop()
	{
		log_assert(!scopes.empty());
		
		auto &scope = scopes.back();
		write(scope.first.str());
		write("\n");
		write(scope.second.str());
		scopes.pop_back();
		
		dedent();
	}
};

struct CxxrtlWriter {
	CxxWriter cxx;

	std::string design_ns = "cxxrtl_design";

	void begin(std::ostream &f)
	{
		cxx.out = &f;

		cxx.writeln("#include <backends/cxxrtl/cxxrtl.h>");
		cxx.writeln();
		cxx.writeln("#if defined(CXXRTL_INCLUDE_CAPI_IMPL) || \\");
		cxx.writeln("    defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)");
		cxx.writeln("#include <backends/cxxrtl/cxxrtl_capi.cc>");
		cxx.writeln("#endif");
		cxx.writeln();
		cxx.writeln("#if defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)");
		cxx.writeln("#include <backends/cxxrtl/cxxrtl_vcd_capi.cc>");
		cxx.writeln("#endif");
		cxx.writeln();
		cxx.writeln("using namespace cxxrtl_yosys;");
		cxx.writeln();
		cxx.writeln("namespace " + design_ns + " {");
		cxx.writeln();
	}

	void end()
	{
		cxx.writeln("} // namespace " + design_ns);
		cxx.writeln();
	}
};

// Async triggers matter because they influence observable behavior.
// Observable behaivor happens in exactly two places: flop state and primary outputs.
// Everything else in the netlist can (and typically will be) optimized out, and then reconstructed
// from the primary inputs and the flop state, using the debug information.
//
// For each bit of the observable state we need to:
// - Allocate a permanent location to store it in the C++ class (which will be accessible by
//   external logic, etc)
// - Collect all of the async triggers that influence it.
//
// Once done, we partition the *bits* into nonoverlapping sets based on the sets of async triggers.
// Each of the sets gets its own eval/commit function pair (which now function entirely based on
// storage needs). While each set gets to influence a number of observable state bits, this does
// not directly correlate with what primary outputs are affected to (since they can be affected
// by any primary inputs) and in complex cases there will be many async domains, one triggered by
// another, eventually feeding each of the primary outputs.

struct TriggerSet {
	enum Polarity {
		Pos = 1,
		Neg = 2,
		Both = 3,
	};

	dict<SigBit, int> bits;

	static TriggerSet singleton(SigBit bit, SyncType sync) 
	{
		TriggerSet set;
		set.insert(bit, sync);
		return set;
	}

	void insert(SigBit bit, SyncType sync) 
	{
		switch(sync) {
			case SyncType::STe:
				bits[bit] = Polarity::Both;
				break;
			case SyncType::STp:
				bits[bit] = bits[bit] | Polarity::Pos;
				break;
			case SyncType::STn:
				bits[bit] = bits[bit] | Polarity::Neg;
				break;
			default:
				log_assert(false);
		}
	}

	vector<std::pair<SigChunk, int>> chunks()
	{
		dict<int, SigSpec> signals;
		vector<std::pair<SigChunk, int>> chunks;
		for (auto it : bits)
			signals[it.second].append(it.first);
		for (auto it : signals) {
			it.second.sort_and_unify();
			for (auto chunk : it.second.chunks())
				chunks.push_back({ chunk, it.first });
		}
		return chunks;
	}

	unsigned int hash() const { return bits.hash(); }

	bool operator==(const TriggerSet &other) const { return bits == other.bits; }

	bool operator!=(const TriggerSet &other) const { return bits != other.bits; }

	TriggerSet &operator|=(const TriggerSet &other) {
		for (auto it: other.bits)
			bits[it.first] |= it.second;
		return *this;
	}

	size_t size() const {
		size_t res = 0;
		for (auto it : bits) {
			if (it.second == Polarity::Both) {
				res += 2;
			} else {
				res += 1;
			}
		}
		return res;
	}
};

struct Domain {
	TriggerSet triggers;
	vector<Cell *> cells;
	pool<SigBit> bits;
	pool<IdString> memories;

	Domain(const TriggerSet &triggers) : triggers(triggers) {}
};

struct CxxrtlModWorker {
	Module *module = nullptr;
	ModWalker *walker;
	SigMap *sigmap;

	vector<Domain> domains;
	dict<TriggerSet, int> domains_dict;

	CxxrtlModWorker(Module *module) : module(module)
	{
		walker = new ModWalker(module->design, module);
		sigmap = &walker->sigmap;
	}

	int get_trigger_set(const TriggerSet &triggers)	{
		if (domains_dict.count(triggers)) {
			return domains_dict[triggers];
		} else {
			int res = domains.size();
			domains.push_back(Domain(triggers));
			domains_dict[triggers] = res;
			return res;
		}
	}

	TriggerSet get_ff_triggers(Cell *cell) {
		FfData ff(nullptr, cell);
		TriggerSet triggers;
		if (ff.has_clk)
			triggers.insert(walker->sigmap(ff.sig_clk), ff.pol_clk ? SyncType::STp : SyncType::STn);
		if (ff.has_aload) {
			for (int i = 0; i < ff.width; i++)
				triggers.insert(walker->sigmap(ff.sig_ad[i]), SyncType::STe);
			triggers.insert(walker->sigmap(ff.sig_aload), ff.pol_aload ? SyncType::STp : SyncType::STn);
		}
		if (ff.has_arst) {
			if (ff.has_aload)
				triggers.insert(walker->sigmap(ff.sig_arst), SyncType::STe);
			else 
				triggers.insert(walker->sigmap(ff.sig_arst), ff.pol_arst ? SyncType::STp : SyncType::STn);
		}
		if (ff.has_sr) {
			for (int i = 0; i < ff.width; i++) {
				triggers.insert(walker->sigmap(ff.sig_clr[i]), SyncType::STe);
				triggers.insert(walker->sigmap(ff.sig_set[i]), SyncType::STe);
			}
		}
		return triggers;
	}

	void analyze_event_domains()
	{
		log_debug("Splitting design into event domains.\n");

		vector<Mem> memories = Mem::get_all_memories(module);
		dict<Cell*, Mem*> rport_to_mem;

		dict<SigBit, int> bit_triggers;
		dict<Cell*, int> cell_triggers;
		dict<IdString, int> memory_triggers;

		TopoSort<Cell*> topo;
		for (auto cell : module->cells()) {
			if (is_pure_cell(cell->type) || (cell->type.in(ID($memrd), ID($memrd_v2)) && !cell->getParam(ID::CLK_ENABLE).as_bool())) {
				topo.node(cell);
				pool<ModWalker::PortBit> drivers;
				for (auto &conn: cell->connections())
					if (cell->input(conn.first))
						for (auto bit: walker->sigmap(conn.second))
							walker->get_drivers(drivers, bit);
				for (auto driver : drivers)
					topo.edge(driver.cell, cell);
			}
		}
		for (auto &mem: memories) {
			for (auto &rport: mem.rd_ports) {
				rport_to_mem[rport.cell] = &mem;
				if (!rport.clk_enable) {
					for (auto &wport: mem.wr_ports) {
						topo.edge(wport.cell, rport.cell);
					}
				} else {
					TriggerSet triggers;
					triggers.insert(walker->sigmap(rport.clk), rport.clk_polarity ? SyncType::STp : SyncType::STn);
					if (!rport.arst.is_fully_const())
						triggers.insert(walker->sigmap(rport.arst), SyncType::STp);
					int tset = get_trigger_set(triggers);
					cell_triggers[rport.cell] = tset;
					for (auto bit: walker->sigmap(rport.data)) {
						bit_triggers[bit] = tset;
						domains[tset].bits.insert(bit);
					}
					domains[tset].cells.push_back(rport.cell);
				}
			}
			TriggerSet mem_triggers;
			for (auto &wport : mem.wr_ports) {
				TriggerSet triggers;
				log_assert(wport.clk_enable);
				triggers.insert(walker->sigmap(wport.clk), wport.clk_polarity ? SyncType::STp : SyncType::STn);
				mem_triggers |= triggers;
				int tset = get_trigger_set(triggers);
				cell_triggers[wport.cell] = tset;
				domains[tset].cells.push_back(wport.cell);
			}
			int tset = get_trigger_set(mem_triggers);
			memory_triggers[mem.memid] = tset;
			domains[tset].memories.insert(mem.memid);
		}

		for (auto cell: module->cells()) {
			if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
				int tset = get_trigger_set(get_ff_triggers(cell));
				cell_triggers[cell] = tset;
				for (auto bit: walker->sigmap(cell->getPort(ID::Q))) {
					bit_triggers[bit] = tset;
					domains[tset].bits.insert(bit);
				}
				domains[tset].cells.push_back(cell);
			}
		}

		topo.sort();

		for (auto cell: topo.sorted) {
			if (is_pure_cell(cell->type) || (cell->type.in(ID($memrd), ID($memrd_v2)) && !cell->getParam(ID::CLK_ENABLE).as_bool())) {
				TriggerSet triggers;
				int inputs_tset;
				bool found_tset = false;
				bool found_trigger = false;
				if (cell->has_memid()) {
					found_tset = true;
					inputs_tset = memory_triggers.at(cell->parameters.at(ID::MEMID).decode_string());
				}
				for (auto &conn : cell->connections())
					if (cell->input(conn.first))
						for (auto bit: walker->sigmap(conn.second)) {
							if (!bit.wire)
								continue;
							if (bit_triggers.count(bit)) {
								int tset = bit_triggers[bit];
								if (found_trigger || (found_tset && inputs_tset != tset)) {
									if (found_tset) {
										triggers = domains[inputs_tset].triggers;
										found_tset = false;
									}
									found_trigger = true;
									triggers |= domains[tset].triggers;
								} else {
									found_tset = true;
									inputs_tset = tset;
								}
							} else {
								if (found_tset) {
									triggers = domains[inputs_tset].triggers;
									found_tset = false;
								}
								found_trigger = true;
								triggers.insert(bit, SyncType::STe);
							}
						}
				if (found_trigger || !found_tset)
					inputs_tset = get_trigger_set(triggers);
				cell_triggers[cell] = inputs_tset;
				for (auto &conn : cell->connections())
					if (cell->output(conn.first))
						for (auto bit: walker->sigmap(conn.second)) {
							if (!bit.wire)
								continue;
							bit_triggers[bit] = inputs_tset;
							domains[inputs_tset].bits.insert(bit);
						}
				domains[inputs_tset].cells.push_back(cell);
			}
		}

		// This dict is invalidated once the domain list is sorted.
		domains_dict.clear();

		// Sort the domain list by trigger set size, as a proxy for the subset-of partial ordering.
		std::sort(domains.begin(), domains.end(), [](const Domain &a, const Domain &b) {
			return a.triggers.size() < b.triggers.size();
		});
	}

	void print_event_domains() 
	{
		log("Printing event domains.\n\n");
		int i = 0;
		for (auto &domain : domains) {
			log("Domain %d @(", i++);
			bool first = true;
			for (auto it: domain.triggers.chunks()) {
				if (first)
					first = false;
				else
					log(", ");
				const char *edge = "";
				if (it.second == 1)
					edge = "posedge ";
				if (it.second == 2)
					edge = "negedge ";
				log("%s%s", edge, log_signal(it.first));
			}
			log(")\n");

			dict<Wire *, SigSpec> wire_bits;
			for (auto bit : domain.bits) {
				log_assert(bit.wire != nullptr);
				wire_bits[bit.wire].append(bit);
			}

			wire_bits.sort<IdString::compare_ptr_by_name<Wire>>();
			for (auto wire_spec : wire_bits) {
				wire_spec.second.sort_and_unify();
				log("\twire %s\n", log_signal(wire_spec.second));
			}
			for (auto cell : domain.cells)
				log("\tcell %s\n", log_id(cell));
			for (auto mem : domain.memories)
				log("\tmemory %s\n", log_id(mem));
		}
	}

	void analyze()
	{
		analyze_event_domains();
	}

	void print_analysis() 
	{
		print_event_domains();
	}

	void write(CxxrtlWriter &writer)
	{
		(void)writer;
		// TODO
	}
};

struct CxxrtlWorker {
	// Options for prepare
	bool run_hierarchy = false;
	bool run_flatten = false;
	bool run_proc = false;
	// Options for analyze
	bool print_analysis = false;

	Design *design;
	vector<CxxrtlModWorker> mod_workers;

	CxxrtlWorker(Design *design) : design(design) {}

	void prepare_design()
	{
		if (run_hierarchy)
			Pass::call(design, "hierarchy -auto-top");
		if (run_flatten)
			Pass::call(design, "flatten");
		if (run_proc)
			Pass::call(design, "proc");
		Pass::call(design, "memory_unpack");

		for (auto module : design->modules()) {
			if (module->get_blackbox_attribute())
				continue;
			if (!design->selected_module(module))
				continue;
			if (!design->selected_whole_module(module))
				log_cmd_error("Can't handle partially selected module `%s'!\n", id2cstr(module->name));
			mod_workers.push_back(CxxrtlModWorker(module));
		}
	}

	void analyze_design()
	{
		for (auto mod_worker : mod_workers) {
			log_header(design, "Analyzing module `%s'.\n", log_id(mod_worker.module->name));
			mod_worker.analyze();
			
			if (print_analysis) {
				log_header(design, "Printing analysis for module `%s'.\n", log_id(mod_worker.module->name));
				mod_worker.print_analysis();
			}
		}
	}

	void write_design(std::ostream *&f, std::string filename)
	{
		// TODO: handle split files, etc
		(void)filename;

		CxxrtlWriter writer;
		writer.begin(*f);

		for (auto mod_worker : mod_workers) {
			log_header(design, "Writing code for module `%s'.\n", log_id(mod_worker.module->name));
			mod_worker.write(writer);
		}

		writer.end();
	}
};

struct Cxxrtl2Backend : public Backend {
	Cxxrtl2Backend() : Backend("cxxrtl2", "convert design to C++ RTL simulation") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_cxxrtl2 [options] [filename]\n");
		log("\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, Design *design) override
	{
		bool nohierarchy = false;
		bool noflatten = false;
		bool noproc = false;
		bool print_analysis = false;

		log_header(design, "Executing CXXRTL2 backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-nohierarchy") {
				nohierarchy = true;
				continue;
			}
			if (args[argidx] == "-noflatten") {
				noflatten = true;
				continue;
			}
			if (args[argidx] == "-noproc") {
				noproc = true;
				continue;
			}
			if (args[argidx] == "-print-analysis") {
				print_analysis = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		CxxrtlWorker worker(design);
		worker.run_hierarchy = !nohierarchy;
		worker.run_flatten = !noflatten;
		worker.run_proc = !noproc;
		worker.print_analysis = print_analysis;

		log_push();
		worker.prepare_design();
		worker.analyze_design();
		worker.write_design(f, filename);
		log_pop();
	}
} Cxxrtl2Backend;

PRIVATE_NAMESPACE_END

//
// CODE GRAVEYARD
//

/*


struct UnionFind {
	struct Inner : std::enable_shared_from_this<Inner> {
		std::shared_ptr<Inner> parent = nullptr;
		bool singleton = true;
	};

	mutable std::shared_ptr<Inner> inner;

	UnionFind() : inner(std::make_shared<Inner>()) {}
	UnionFind(const UnionFind &other) : inner(other.inner) {}
	UnionFind(const std::shared_ptr<Inner> &inner) : inner(inner) {}
	UnionFind &operator=(const UnionFind &other) { inner = other.inner; return *this; }

	void unify(UnionFind &other) {
		find().inner->parent = other.inner;
		find().inner->singleton = false;
	}

	UnionFind find() const {
		if (inner->parent) {
			while (inner->parent->parent)
				inner->parent = inner->parent->parent;
			return UnionFind(inner->parent);
		} else {
			return *this;
		}
	}

	bool singleton() const {
		return find().inner->singleton;
	}

	unsigned int hash() const { 
		return (uintptr_t)&*find().inner;
	}

	bool operator==(UnionFind other) const {
		return &*find().inner == &*other.find().inner;
	}

	bool operator!=(UnionFind &other) const {
		return !(*this == other);
	}
};

*/

/*
	dict<SigBit, int> bit_domains;
	dict<Cell*, int> cell_domains;
*/


#if 0
		// Domain 0 should never appear anywhere; if it appears it indicates a bug.
		int next_domain = 1;

		// Each primary input is its own trigger.
		for (auto wire : module->wires())
			for (auto bit : walker->sigmap(wire))
				bit_triggers[bit] = TriggerSet::singleton(bit, SyncType::STe);

/*
		// Each bit gets its own domain initially.
		for (auto wire : module->wires())
			for (auto bit : walker->sigmap(wire))
				bit_domains[bit] = next_domain++; // creates a domain
*/

		// Combine domains of flip-flops with identical asynchronous control set together.
		dict<TriggerSet, vector<Cell*>> async_control_sets;
		for (auto cell : module->cells()) {
			if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
				TriggerSet triggers = get_ff_triggers(cell);
				async_control_sets[triggers].push_back(cell);
			}
		}

		for (auto async_control_set : async_control_sets)
			for (auto cell : async_control_set.second) {
				cell_triggers[cell] = async_control_set.first;
				for (auto bit : walker->sigmap(cell->getPort(ID::Q)))
					bit_triggers[bit] = async_control_set.first;
			}

/*
		// The outputs of a storage cell are in the same domain as its async control set.
		for (auto it : async_control_sets) {
			int domain = next_domain++;
			for (auto cell : it.second) {
				cell_domains[cell] = domain;
				for (auto bit : walker->sigmap(cell->getPort(ID::Q)))
					bit_domains[bit] = domain;
			}
		}
*/

		// Unify the domain of a combinational cell with the domain of its inputs if all of the
		// inputs are in the same domain.
		pool<Cell*> worklist;
		for (auto cell : module->cells()) {
			if (is_pure_cell(cell->type)) {
				int domain = next_domain++;
				// All outputs of a combinatorial cell are in the same domain.
				cell_domains[cell] = domain;
				for (auto &conn : cell->connections())
					if (cell->output(conn.first)) {
						log_assert(!cell->input(conn.first));
						for (auto bit : walker->sigmap(conn.second)) {
							if (!bit.wire) 
								continue;
							bit_domains[bit] = domain;
						}
					}

				worklist.insert(cell);
			}
		}
		while (!worklist.empty()) {
			Cell *cell = worklist.pop();
			if (!is_pure_cell(cell->type)) continue;
	
			int domain = 0;
			bool found_input_domain = false, all_inputs_in_domain = true;
			log_debug("Considering input domains of cell %s\n", log_id(cell));
			for (auto &conn : cell->connections())
				if (cell->input(conn.first)) {
					log_assert(!cell->output(conn.first));
					for (auto bit : walker->sigmap(conn.second)) {
						if (!bit.wire)
							continue;
						int input_domain = bit_domains[bit];
						if (!found_input_domain) {
							domain = input_domain;
							found_input_domain = true;
						} else if (domain != input_domain)
							all_inputs_in_domain = false;
					}
				}
			if (!all_inputs_in_domain)
				continue;
			if (domain == cell_domains[cell])
				continue;
			log_debug("All inputs of cell %s are in the same domain\n", log_id(cell));
			cell_domains[cell] = domain;
			for (auto &conn : cell->connections())
				if (cell->output(conn.first)) {
					log_assert(!cell->input(conn.first));
					for (auto bit : walker->sigmap(conn.second)) {
						if (!bit.wire) 
							continue;
						bit_domains[bit] = domain;
						pool<ModWalker::PortBit> consumers;
						walker->get_consumers(consumers, bit);
						for (auto consumer : consumers) {
							log_debug("Revisiting cell %s\n", log_id(consumer.cell));
							worklist.insert(consumer.cell);
						}
 					}
				}
		}
#endif

/*
struct RtlWorkItem {
	enum class Type {
		CONNECT,
		CELL_EVAL,
	};

	Type type;
	SigSig connect = {};
	Cell *cell = nullptr;

	pool<SigBit> outputs;
	pool<SigBit> inputs;
	dict<SigBit, SyncType> triggers;

	RtlWorkItem(SigSig connect_)
	{
		type = Type::CONNECT;
		connect = connect_;
		outputs.insert(connect.second.begin(), connect.second.end());
		inputs.insert(connect.first.begin(), connect.first.end());
		for (SigBit &input : connect.first)
			triggers[input] = STe;
	}

	RtlWorkItem(Cell *cell_) {
		type = Type::CELL_EVAL;
		cell = cell_;
		for (auto conn : cell->connections()) {
			if (cell->output(conn.first))
				outputs.insert(conn.second);
			if (cell->input(conn.first))
				inputs.insert(conn.second);
		}
		if (is_internal_cell(cell->type)) {
			if (is_pure_cell(cell->type) || is_latch_cell(cell->type)) {
				for (SigBit &input : inputs)
					triggers[input] = STe;
			} else if (is_ff_cell(cell->type)) {
				SigBit clk = cell->getPort(ID::CLK)[0];
				if (clk.is_wire())
					triggers[clk] = cell->parameters.at(ID::CLK_POLARITY).as_bool() ? STp : STn;
			}
		} else {
			log_assert(false);
		}
	}
};

struct RtlWorkGroup {

};
*/

/*

	dict<Cell*, Cell*> cell_mffcs; // cell -> cell whose MFFC it is in

	void set(Module *module)
	{
		this->module = module;
		walker = new ModWalker(module->design, module);
		sigmap = &walker->sigmap;
	}

	void analyze_fanout()
	{
		log_debug("Computing maximum fanout free cones.\n");
		pool<Cell*> worklist;
		for (auto cell : module->cells())
			if (is_pure_cell(cell->type)) {
				cell_mffcs[cell] = cell;
				worklist.insert(cell);
			}
		while (!worklist.empty()) {
			Cell *cell = worklist.pop();
			pool<ModWalker::PortBit> drivers;
			for (auto conn : cell->connections())
				if (cell->input(conn.first))
					walker->get_drivers(drivers, conn.second);
			for (auto driver : drivers) {
				if (!cell_mffcs.count(driver.cell) || cell_mffcs[driver.cell] == cell_mffcs[cell])
					continue;
				pool<Cell *> consumers_for_driver;
				for (auto conn : driver.cell->connections())
					if (cell->output(conn.first)) {
						pool<ModWalker::PortBit> consumers;
						walker->get_consumers(consumers, conn.second);
						for (auto consumer : consumers)
							consumers_for_driver.insert(consumer.cell);
					}
				bool all_consumers_in_mffc = true;
				for (auto consumer : consumers_for_driver)
					if (cell_mffcs.count(consumer) && cell_mffcs[consumer] != cell_mffcs[cell])
						all_consumers_in_mffc = false;
				if (all_consumers_in_mffc) {
					log_debug("MFFC of %s is now %s\n", log_id(driver.cell), log_id(cell_mffcs[cell]));
					cell_mffcs[driver.cell] = cell_mffcs[cell];
					worklist.insert(driver.cell);
				}
			}
		}
	}

	void print_fanout()
	{
		log("Printing maximum fanout free cones.\n");
		dict<Cell*, pool<Cell*>> mffcs;
		for (auto cell_mffc : cell_mffcs)
			mffcs[cell_mffc.second].insert(cell_mffc.first);
		for (auto mffc : mffcs) {
			log("Cell %s\n", log_id(mffc.first));
			for (auto node : mffc.second)
				log("\t%s\n", log_id(node));
		}
	}

*/