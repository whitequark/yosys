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
	// to be filled in later
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

struct TriggerSet {
	enum Polarity {
		Pos = 1,
		Neg = 2,
		Both = 3,
	};

	dict<SigBit, int> bits;

	void insert(SigBit bit, SyncType sync) {
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

	unsigned int hash() const { return bits.hash(); }

	bool operator==(const TriggerSet &other) const { return bits == other.bits; }

	bool operator!=(const TriggerSet &other) const { return bits != other.bits; }
};

struct ObservableBit {
	SigBit bit;
	UnionFind domain;

	static std::vector<ObservableBit> from(SigSpec sigspec) {
		std::vector<ObservableBit> bits;
		for (auto bit : sigspec)
			bits.emplace_back(bit);
		return bits;
	}

	ObservableBit(SigBit bit_) : bit(bit_) {}
};

struct CxxrtlModWorker {
	Module *module = nullptr;
	ModWalker *walker;
	SigMap *sigmap;
	dict<Cell*, Cell*> cell_mffcs; // cell -> cell whose MFFC it is in
	dict<SigBit, UnionFind> bit_domains;

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
				pool<Cell*> consumers_for_driver;
				for (auto conn : driver.cell->connections())
					if (cell->output(conn.first)) {
						pool<ModWalker::PortBit> consumers;
						walker->get_consumers(consumers, conn.second);
						for (auto consumer : consumers)
							consumers_for_driver.insert(consumer.cell);
					}
				bool all_consumers_in_mffc = true;
				for (auto consumer : consumers_for_driver)
					if (cell_mffcs.count(consumer) && cell_mffcs[consumer] != cell)
						all_consumers_in_mffc = false;
				if (all_consumers_in_mffc) {
					cell_mffcs[driver.cell] = cell;
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

	void analyze_bit_domains()
	{
		log_debug("Splitting design into event domains.\n");

		// Each bit gets its own domain initially.
		for (auto wire : module->wires())
			for (auto bit : SigSpec(wire))
				bit_domains[bit]; // creates a domain

		// Combine domains of flip-flops with identical asynchronous control set together.
		dict<TriggerSet, vector<Cell*>> async_control_sets;
		for (auto cell : module->cells()) {
			if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
				FfData ff(nullptr, cell);
				TriggerSet triggers;
				if (ff.has_clk)
					triggers.insert(ff.sig_clk, ff.pol_clk ? SyncType::STp : SyncType::STn);
				if (ff.has_aload) {
					for (int i = 0; i < ff.width; i++)
						triggers.insert(ff.sig_ad[i], SyncType::STe);
					triggers.insert(ff.sig_aload, ff.pol_aload ? SyncType::STp : SyncType::STn);
				}
				if (ff.has_arst) {
					if (ff.has_aload)
						triggers.insert(ff.sig_arst, SyncType::STe);
					else 
						triggers.insert(ff.sig_arst, ff.pol_arst ? SyncType::STp : SyncType::STn);
				}
				if (ff.has_sr) {
					for (int i = 0; i < ff.width; i++) {
						triggers.insert(ff.sig_clr[i], SyncType::STe);
						triggers.insert(ff.sig_set[i], SyncType::STe);
					}
				}
				async_control_sets[triggers].push_back(cell);
			}
		}

		// The outputs of a storage cell are in the same domain as its async control set.
		for (auto it : async_control_sets) {
			UnionFind domain;
			for (auto cell : it.second)
				for (auto bit : cell->getPort(ID::Q))
					bit_domains[walker->sigmap(bit)].unify(domain);
		}

		// Unify the domain of a combinational cell with the domain of its inputs if all of the
		// inputs are in the same domain.
		pool<Cell*> worklist;
		for (auto cell : module->cells())
			worklist.insert(cell);
		while (!worklist.empty()) {
			Cell *cell = worklist.pop();
			if (!is_pure_cell(cell->type)) continue;
	
			UnionFind domain;
			bool found_input_domain = false, all_inputs_in_domain = true;
			log_debug("Considering input domains of cell %s\n", log_id(cell));
			for (auto &conn : cell->connections())
				if (cell->input(conn.first)) {
					log_assert(!cell->output(conn.first));
					for (auto bit : walker->sigmap(conn.second)) {
						if (!bit.wire)
							continue;
						UnionFind input_domain = bit_domains[bit].find();
						if (!found_input_domain) {
							domain = input_domain;
							found_input_domain = true;
						} else if (domain != input_domain)
							all_inputs_in_domain = false;
					}
				}
			if (!all_inputs_in_domain)
				continue;
			log_debug("All inputs of cell %s are in the same domain\n", log_id(cell));
			bool changed = false;
			for (auto &conn : cell->connections())
				if (cell->output(conn.first)) {
					log_assert(!cell->input(conn.first));
					for (auto bit : walker->sigmap(conn.second)) {
						if (!bit.wire) 
							continue;
						UnionFind output_domain = bit_domains[bit];
						if (output_domain.singleton()) {
							log_debug("Unifying output %s with input domain\n", log_signal(bit));
							output_domain.unify(domain);
							changed = true;
						}
					}
				}
			if (changed) {
				for (auto &conn : cell->connections())
					if (cell->output(conn.first)) {
						for (auto bit : walker->sigmap(conn.second)) {
							if (!bit.wire) 
								continue;
							pool<ModWalker::PortBit> consumers;
							walker->get_consumers(consumers, bit);
							for (auto consumer : consumers) {
								log_debug("Revisiting cell %s\n", log_id(consumer.cell));
								worklist.insert(consumer.cell);
							}
 						}
					}
			}
		}
		
		
	}

	void print_bit_domains() 
	{
		log("Printing bit domains.\n\n");
		dict<UnionFind, int> names;
		for (auto bit_domain : bit_domains)
			if (!names.count(bit_domain.second.find()))
				names[bit_domain.second.find()] = names.size();
		for (auto domain_name : names) { // iterates in reverse order, so we reverse again
			log("Domain %zu:\n", names.size() - domain_name.second - 1);
			for (auto bit_domain : bit_domains)
				if (bit_domain.second == domain_name.first)
					log("\t%s\n", log_signal(bit_domain.first));
		}
	}

	void analyze()
	{
		analyze_fanout();
		analyze_bit_domains();
	}

	void print_analysis() {
		print_fanout();
		print_bit_domains();
	}
};

struct CxxrtlWorker {
	// Options for prepare
	bool run_hierarchy = false;
	bool run_flatten = false;
	bool run_proc = false;
	// Options for analyze
	bool print_analysis = false;

	dict<const Module*, CxxrtlModWorker> mod_workers;

	void prepare_design(Design *design)
	{
		for (auto module : design->modules()) {
			if (module->get_blackbox_attribute())
				continue;
			if (!design->selected_module(module))
				continue;
			if (!design->selected_whole_module(module))
				log_cmd_error("Can't handle partially selected module `%s'!\n", id2cstr(module->name));
		}

		log_push();
		if (run_hierarchy)
			Pass::call(design, "hierarchy -auto-top");
		if (run_flatten)
			Pass::call(design, "flatten");
		if (run_proc)
			Pass::call(design, "proc");
		log_pop();
	}

	void analyze_design(Design *design)
	{
		for (auto module : design->modules()) {
			if (!design->selected_module(module))
				continue;

			CxxrtlModWorker &mod_worker = mod_workers[module];
			mod_worker.set(module);
			mod_worker.analyze();
			if (print_analysis)
				mod_worker.print_analysis();
		}
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
		CxxrtlWorker worker;

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

		worker.run_hierarchy = !nohierarchy;
		worker.run_flatten = !noflatten;
		worker.run_proc = !noproc;
		worker.print_analysis = print_analysis;

		worker.prepare_design(design);
		worker.analyze_design(design);
	}
} Cxxrtl2Backend;

PRIVATE_NAMESPACE_END


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
