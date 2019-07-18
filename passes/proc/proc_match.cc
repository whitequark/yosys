/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019  whitequark <whitequark@whitequark.org>
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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"

// [[CITE]] Optimizing ML pattern matching
// Le Fessant, Fabrice, and Luc Maranget. "Optimizing pattern matching." ICFP. Vol. 1. 2001.
// http://moscova.inria.fr/~maranget/papers/opt-pat.ps.gz

// [[CITE]] Dominance algorithm
// Cooper, Keith D., Timothy J. Harvey, and Ken Kennedy. "A simple, fast dominance algorithm."
// Software Practice & Experience 4.1-10 (2001): 1-8.
// https://www.cs.rice.edu/~keith/EMBED/dom.pdf

// The design of this pass borrows three well-known computing science methods and applies them to logic synthesis:
//   1. continuation-passing style transformation, and
//   2. ML-style pattern matching optimization, and
//   3. sparse conditional constant propagation.
// Together, they are used to convert the RTLIL representation of processes into something closely resembling a traditional
// compiler IR, where decision points and assignments become basic blocks.
//
// The first method, CPS transformation, is useful because RTLIL processes use sequential semantics and implicit sharing
// of behavior; that is, when two RTLIL switches with n and m cases are sequenced, the behavior they encode is shared such
// that n*m cases are represented with n+m operations, avoiding a combinatorial explosion. Unfortunately, sequential
// semantics does not match multiplexer trees well. To handle this, RTLIL processes are CPS-transformed, such that, for two
// switches in sequence, each case of the first switch is followed by the entirety of the second switch. This representation
// uses explicit sharing of behavior by reusing the basic blocks.
//
// The second method, ML-style pattern matching optimization, is used for optimization of individual switches themselves.
// One can note that RTLIL signals are equivalent to tuples of booleans, don't cares are equivalent to wildcard patterns,
// and multiple compare clauses per case rule are equivalent to or-patterns. ML-style pattern matching is not trivial to
// compile in linear size, but, fortunately, this is a well-researched problem.
//
// The third method, sparse conditional constant propagation, is used to push assigns across decision points, such that
// at different points in the pass they are (a) grouped into control independent sets, and (b) are affected by decision
// points as early as possible. In both cases, the end result is minimizing the amount of muxes, and the amount of bits
// per mux.

// This pass consists of several subpasses, carefully invoked in the right sequence. These are:
//   1. Build initial IR.
//   2. Deduplicate. This subpass removes any syntactic redundancy in the input.
//   3. Fold decisions. This subpass uses a lattice to eliminate repeated decisions on the same input bit.
//   4. Cleanup. This subpass removes any edges made impossible by the previous subpass, and makes the following subpass
//      more precise.
//   5. Sink assigns. This subpass uses a lattice to propagate assigns towards the exit block, and then removes any
//      assigns that are overridden by all successors, thereby moving assigns across the switches that do not affect them,
//      and making them topologically closer to the decisions that do, and makes the following subpass useful.
//   6. Cut graph. This subpass uses dominator analysis to split the graph into multiple control independent subgraphs
//      that assign to distinct sets of bits, making the independence explicit.
//   7. Hoist assigns. This subpass uses a lattice to propagate assigns towards the entry block, and then removes any
//      assigns that are overridden by all predecessors, thereby making sure decisions affect assigns as early as possible,
//      and minimizing the amount of bits that are multiplexed.
//   8. Deduplicate. This subpass removes any additional redundancy exposed by the previous pass.

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

typedef std::shared_ptr<struct BasicBlock> SharedBasicBlock;
struct BasicBlock
{
	// Instructions
	std::vector<RTLIL::SigSig> actions;
	// Terminator
	RTLIL::SigBit cond = RTLIL::State::Sx;
	SharedBasicBlock if0, if1;

	bool is_useless() const {
		if (!actions.empty()) return false;
		if (cond == State::S0 || cond == State::S1) return true;
		if (if0 == if1) return if0 != nullptr; // keep exit block
		return false;
	}

	SharedBasicBlock succ() {
		if (cond == State::S0) return if0;
		if (cond == State::S1) return if1;
		log_assert(if0 == if1);
		return if0;
	}
};

PRIVATE_NAMESPACE_END

template<> struct hash_ops<SharedBasicBlock> {
	static inline bool cmp(const SharedBasicBlock &a, const SharedBasicBlock &b) {
		return a == b;
	}
	static inline unsigned int hash(const SharedBasicBlock &a) {
		return (uintptr_t)a.get();
	}
};

struct hash_block_equiv_ops {
	static inline bool cmp(SharedBasicBlock a, SharedBasicBlock b) {
		if (a == nullptr || b == nullptr) return a == b;
		return a->actions == b->actions && a->cond == b->cond && a->if0 == b->if0 && a->if1 == b->if1;
	}
	static inline unsigned int hash(SharedBasicBlock a) {
		if (a == nullptr) return 0;
		unsigned int hash = mkhash_init;
		for (auto &act : a->actions)
			hash = mkhash(hash, hash_ops<RTLIL::SigSig>::hash(act));
		hash = mkhash(hash, a->cond.hash());
		// Any successors assumed to already be normalized, so they can be compared by pointer.
		hash = mkhash(hash, (uintptr_t)a->if0.get());
		hash = mkhash(hash, (uintptr_t)a->if1.get());
		return hash;
	}
};

PRIVATE_NAMESPACE_BEGIN

struct FlowGraph {
	string name;
	SharedBasicBlock entry;

	void dump_graphviz(string filename);

	// Analyses
	size_t order();
	dict<SharedBasicBlock, pool<SharedBasicBlock>> predecessors();
	std::vector<SharedBasicBlock> postorder(bool reverse=false);
	dict<SharedBasicBlock, SharedBasicBlock> dominators();

	// Transforms
	void cleanup();
	void deduplicate();
	void fold_decisions();
	std::vector<FlowGraph> split_independent();
	void sink_assigns();
	void hoist_assigns();
	void insert_phis(RTLIL::Module *module);
};

static string dot_escape(string value, int wrap_at = -1)
{
	int pos = 0;
	std::string escaped;
	for (char c : value) {
		if (c == '\n' || (++pos >= wrap_at && c == ' ')) {
			pos = 0;
			escaped += "\\n";
			continue;
		}
		if (c == '\\' || c == '"')
			escaped += "\\";
		escaped += c;
	}
	return escaped;
}

void FlowGraph::dump_graphviz(string filename)
{
	FILE *f = fopen(filename.c_str(), "w");
	fprintf(f, "digraph \"%s\" {\n", name.c_str());
	fprintf(f, "  rankdir=\"TB\";\n");

	idict<SharedBasicBlock> ids;
	pool<SharedBasicBlock> worklist = {entry}, visited = {};

	ids.expect(nullptr, 0);
	visited.insert(nullptr);
	fprintf(f, "  n0 [ label=\"k\", color=\"red\" ]\n");

	while (!worklist.empty())
	{
		SharedBasicBlock block = worklist.pop();
		if (visited.count(block)) continue;
		visited.insert(block);
		worklist.insert(block->if0);
		worklist.insert(block->if1);

		string label;
		label += stringf("%p\n", block.get());
		for (auto &act : block->actions)
			label += stringf("%s <= %s\n", log_signal(act.first), log_signal(act.second));
		if (block->cond != State::Sx)
			label += stringf("%s ?", log_signal(block->cond));
		if (label.empty())
			label += "<empty>";
		string color = "black";
		if(!block->actions.empty())
			color = "blue";
		else if (block->is_useless())
			color = "green";
		fprintf(f, "  n%d [ fontname=\"Monospace\", label=\"%s\", color=\"%s\" ];\n",
		        ids(block), dot_escape(label, 40).c_str(), color.c_str());
		if (block->if0 == block->if1)
			fprintf(f, "  n%d -> n%d [ penwidth=2 ];\n", ids(block), ids(block->if0));
		else {
			fprintf(f, "  n%d -> n%d [ label=\"0\", style=\"dashed\" ];\n", ids(block), ids(block->if0));
			fprintf(f, "  n%d -> n%d [ label=\"1\", style=\"solid\"  ];\n", ids(block), ids(block->if1));
		}
	}

	fprintf(f, "}\n");
	fclose(f);
}

size_t FlowGraph::order()
{
	size_t order = 0;
	pool<SharedBasicBlock> worklist = {entry}, visited = {nullptr};
	while (!worklist.empty()) {
		SharedBasicBlock block = worklist.pop();
		if (visited.count(block)) continue;
		visited.insert(block);
		worklist.insert(block->if0);
		worklist.insert(block->if1);
		order++;
	}
	return order;
}

dict<SharedBasicBlock, pool<SharedBasicBlock>> FlowGraph::predecessors()
{
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds;
	pool<SharedBasicBlock> worklist = {entry}, visited = {nullptr};
	while (!worklist.empty()) {
		SharedBasicBlock block = worklist.pop();
		if (visited.count(block)) continue;
		visited.insert(block);
		worklist.insert(block->if0);
		worklist.insert(block->if1);
		preds[block->if0].insert(block);
		preds[block->if1].insert(block);
	}
	return preds;
}

std::vector<SharedBasicBlock> FlowGraph::postorder(bool reverse)
{
	std::vector<SharedBasicBlock> postorder;
	std::vector<std::pair<SharedBasicBlock, bool>> worklist = {{entry, /*seen=*/false}};
	pool<SharedBasicBlock> visited;
	while (!worklist.empty()) {
		std::pair<SharedBasicBlock, bool> block_seen = worklist.back();
		worklist.pop_back();
		if (block_seen.second)
			postorder.push_back(block_seen.first);
		else if (!visited.count(block_seen.first)) {
			visited.insert(block_seen.first);
			worklist.push_back({block_seen.first, /*seen=*/true});
			if (block_seen.first != nullptr) {
				worklist.push_back({block_seen.first->if0, /*seen=*/false});
				worklist.push_back({block_seen.first->if1, /*seen=*/false});
			}
		}
	}
	if (reverse)
		std::reverse(postorder.begin(), postorder.end());
	return postorder;
}

dict<SharedBasicBlock, SharedBasicBlock> FlowGraph::dominators()
{
	// Algorithm by Cooper et al.
	idict<SharedBasicBlock> postorder;
	for (auto &block : this->postorder()) postorder(block);
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds = predecessors();
	dict<SharedBasicBlock, SharedBasicBlock> doms;
	doms[entry] = entry;
	bool changed = true;
	while (changed) {
		changed = false;
		for (auto &block : postorder) { // idict iterates in reverse
			SharedBasicBlock new_idom;
			for (auto &pred : preds[block])
				if (doms.count(pred)) {
					new_idom = pred;
					break;
				}
			for (auto &pred : preds[block])
				if (doms.count(pred) && pred != new_idom) {
					SharedBasicBlock finger = pred;
					while (new_idom != finger) {
						while (postorder.at(new_idom) < postorder.at(finger))
							new_idom = doms[new_idom];
						while (postorder.at(finger) < postorder.at(new_idom))
							finger = doms[finger];
					}
				}
			if (doms[block] != new_idom) {
				doms[block] = new_idom;
				changed = true;
			}
		}
	}
	return doms;
}

void FlowGraph::cleanup()
{
	// Find and eliminate useless nodes.
	pool<SharedBasicBlock> worklist = {entry}, visited = {nullptr};
	while (!worklist.empty()) {
		SharedBasicBlock node = worklist.pop();
		if (visited.count(node)) continue;
		visited.insert(node);
		while (node->if0 && node->if0->is_useless()) node->if0 = node->if0->succ();
		while (node->if1 && node->if1->is_useless()) node->if1 = node->if1->succ();
		if (node->if0) worklist.insert(node->if0);
		if (node->if1) worklist.insert(node->if1);
	}
	while (entry != nullptr && entry->is_useless())
		entry = entry->succ();
}

void FlowGraph::deduplicate()
{
	// Merge identical nodes.
	pool<SharedBasicBlock, hash_block_equiv_ops> unique;
	for (auto &block : postorder()) {
		if (block != nullptr) {
			auto it0 = unique.find(block->if0);
			if (it0 != unique.end()) block->if0 = *it0;
			auto it1 = unique.find(block->if1);
			if (it1 != unique.end()) block->if1 = *it1;
		}
		if (!unique[block])
			unique.insert(block);
	}
	if (unique.count(entry))
		entry = *unique.find(entry);
}

template<class Value>
static void update_lattice(dict<RTLIL::SigBit, Value> &state, RTLIL::SigBit sig, Value value)
{
	// top = missing from state; bottom = State::Sa.
	if (!state.count(sig))
		state[sig] = value;
	else if (state[sig] != value)
		state[sig] = State::Sa;
}

void FlowGraph::fold_decisions()
{
	// Eliminate blocks whose decision is predetermined by an earlier block.
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds = predecessors();
	dict<SharedBasicBlock, dict<RTLIL::SigBit, RTLIL::State>> states;
	for (auto &block : postorder(/*reverse=*/true)) {
		dict<RTLIL::SigBit, RTLIL::State> state;
		for (auto &pred : preds[block]) {
			log_assert(states.count(pred));
			for (auto &bit_value : states[pred])
				update_lattice(state, bit_value.first, bit_value.second);
			if (pred->cond != State::Sa && block == pred->if0)
				update_lattice(state, pred->cond, State::S0);
			if (pred->cond != State::Sa && block == pred->if1)
				update_lattice(state, pred->cond, State::S1);
		}
		states[block] = state;
		if (block == nullptr)
			continue;
		if (state.count(block->cond) && state[block->cond] != State::Sa)
			block->cond = state[block->cond]; // and removed later in a cleanup pass
	}
}

std::vector<FlowGraph> FlowGraph::split_independent()
{
	// Cut flow graph into components that assign to non-intersecting sets of signals.
	// First, count the amount of assigns to each bit.
	dict<RTLIL::SigBit, int> counts;
	pool<SharedBasicBlock> worklist = {entry}, visited = {nullptr};
	while (!worklist.empty()) {
		SharedBasicBlock block = worklist.pop();
		if (visited.count(block)) continue;
		visited.insert(block);
		worklist.insert(block->if0);
		worklist.insert(block->if1);
		for (auto &action : block->actions)
			for (auto &bit : action.first)
				counts[bit]++;
	}
	// Second, try cutting at each immediate dominator of the exit node, such that each cut results in a subgraph
	// containing all assigns in the entire graph to any bit it assigns at least once.
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds = predecessors();
	dict<SharedBasicBlock, SharedBasicBlock> doms = dominators();
	std::vector<SharedBasicBlock> cuts;
	dict<RTLIL::SigBit, int> cut_counts;
	SharedBasicBlock curr_cut = nullptr;
	while (doms[curr_cut] != nullptr) {
		// Iterate the graph from previous considered cut to current considered cut.
		worklist = preds[curr_cut];
		curr_cut = doms[curr_cut];
		visited  = preds[curr_cut];
		while (!worklist.empty()) {
			SharedBasicBlock block = worklist.pop();
			if (visited.count(block)) continue;
			visited.insert(block);
			if (block == nullptr) continue;
			worklist.insert(preds[block].begin(), preds[block].end());
			for (auto &action : block->actions)
				for (auto &bit : action.first)
					cut_counts[bit]++;
		}
		// Check if the subgraph from previous actual cut to current considered cut is valid.
		bool valid_cut = true;
		for (auto &bit_count : cut_counts)
			if (counts[bit_count.first] != bit_count.second){
				valid_cut = false;
				break;
			}
		// If the current considered cut is valid and not useless, make it an actual cut.
		if (valid_cut && !cut_counts.empty()) {
			cuts.push_back(curr_cut);
			cut_counts.clear();
		}
	}
	for (auto &cut : cuts)
		for (auto &pred : preds[cut]) {
			if (pred->if0 == cut) pred->if0 = nullptr;
			if (pred->if1 == cut) pred->if1 = nullptr;
		}
	if (cuts.empty())
		cuts.push_back(entry);
	std::vector<FlowGraph> subgraphs;
	for (auto it = cuts.rbegin(); it != cuts.rend(); ++it)
		subgraphs.push_back({ stringf("%s-%td", name.c_str(), it - cuts.rbegin()), *it });
	return subgraphs;
}

static std::vector<RTLIL::SigSig> collect_actions(dict<RTLIL::SigBit, RTLIL::SigBit> &bits)
{
	std::vector<RTLIL::SigSig> actions;
	bits.sort();
	for (auto &bit_value : bits) {
		if (actions.empty())
			actions.push_back({});
		else if (!actions.back().first.empty() && actions.back().first[0].wire != bit_value.first.wire)
			actions.push_back({});
		actions.back().first.append(bit_value.first);
		actions.back().second.append(bit_value.second);
	}
	return actions;
}

void FlowGraph::sink_assigns()
{
	// Push assigned bits that are not control-dependent towards the exit block.
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds = predecessors();
	dict<SharedBasicBlock, dict<RTLIL::SigBit, RTLIL::SigBit>> states;
	for (auto &block : postorder(/*reverse=*/true)) {
		dict<RTLIL::SigBit, RTLIL::SigBit> state;
		for (auto &pred : preds[block]) {
			log_assert(states.count(pred));
			for (auto &bit_value : states[pred])
				update_lattice(state, bit_value.first, bit_value.second);
		}
		if (block == nullptr)
			continue;
		for (auto &act : block->actions)
			for (int bit = 0; bit < act.first.size(); bit++)
				state[act.first[bit]] = act.second[bit];
		states[block] = state;
	}
	// And replace the actions with our refinement.
	for (auto &block_state : states) {
		dict<RTLIL::SigBit, RTLIL::SigBit> compact_state;
		SharedBasicBlock &block = block_state.first;
		for (auto &bit_value : block_state.second) {
			// Omit bottom bits, since they're defined by a predecessor.
			if (bit_value.second == State::Sa) continue;
			// Omit bits defined by all successors.
			if (block->if0 && states[block->if0].count(bit_value.first) &&
			    	states[block->if0][bit_value.first] != State::Sa &&
			    block->if1 && states[block->if1].count(bit_value.first) &&
			    	states[block->if1][bit_value.first] != State::Sa) continue;
			// Include the rest.
			compact_state[bit_value.first] = bit_value.second;
		}
		block->actions = collect_actions(compact_state);
	}
}

void FlowGraph::hoist_assigns()
{
	// Push assigned bits that are not control-dependent towards the entry block.
	dict<SharedBasicBlock, dict<RTLIL::SigBit, RTLIL::SigBit>> states;
	states[nullptr] = {};
	for (auto &block : postorder()) {
		if (block == nullptr) continue;
		log_assert(states.count(block->if0) && states.count(block->if1));
		dict<RTLIL::SigBit, RTLIL::SigBit> state;
		for (auto &bit_value : states[block->if0])
			update_lattice(state, bit_value.first, states[block->if1].count(bit_value.first) ? bit_value.second : State::Sa);
		for (auto &bit_value : states[block->if1])
			update_lattice(state, bit_value.first, states[block->if0].count(bit_value.first) ? bit_value.second : State::Sa);
		for (auto &act : block->actions)
			for (int bit = 0; bit < act.first.size(); bit++)
				state[act.first[bit]] = act.second[bit];
		states[block] = state;
	}
	// And replace the actions with our refinement.
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds = predecessors();
	for (auto &block_state : states) {
		if (block_state.first == nullptr) continue;
		dict<RTLIL::SigBit, RTLIL::SigBit> compact_state;
		SharedBasicBlock &block = block_state.first;
		for (auto &bit_value : block_state.second) {
			// Omit bottom bits, since they're defined by a successor.
			if (bit_value.second == State::Sa) continue;
			// Omit bits defined to the same value by all predecessors.
			bool all_preds_same = !preds[block].empty();
			for (auto &pred : preds[block])
				if (!(states[pred].count(bit_value.first) && states[pred][bit_value.first] == bit_value.second)) {
					all_preds_same = false;
					break;
				}
			if (all_preds_same) continue;
			// Include the rest.
			compact_state[bit_value.first] = bit_value.second;
		}
		block->actions = collect_actions(compact_state);
	}
}

typedef std::pair<RTLIL::SigBit, int> SigBitSSA;
typedef std::pair<RTLIL::Wire*, int> WireSSA;
void FlowGraph::insert_phis(RTLIL::Module *module)
{
	// Make path dependence of values explicit.
	dict<SharedBasicBlock, pool<SharedBasicBlock>> preds = predecessors();
	idict<SharedBasicBlock> indexes; // in reverse postorder
	dict<SigBitSSA, pool<SigBitSSA>> phis;
	dict<WireSSA, RTLIL::Wire*> phi_wires;
	dict<SharedBasicBlock, dict<RTLIL::SigBit, SigBitSSA>> values;
	for (auto &block : postorder(/*reverse=*/true)) {
		int block_index = indexes(block);
		dict<RTLIL::SigBit, SigBitSSA> &block_values = values[block];
		if (block != nullptr) {
			for (auto &act : block->actions)
				for (int bit = 0; bit < act.first.size(); bit++)
					block_values[act.first[bit]] = {act.second[bit], block_index};
		}
		dict<RTLIL::SigBit, pool<SigBitSSA>> new_phis;
		for (auto &pred : preds[block])
			for (auto &bit_ssa : values[pred]) {
				if (block_values.count(bit_ssa.first)) continue;
				new_phis[bit_ssa.first].insert(bit_ssa.second);
			}
		for (auto &bit_incoming : new_phis) {
			RTLIL::SigBit &bit = bit_incoming.first;
			const pool<SigBitSSA> &incoming = bit_incoming.second;
			if (incoming.size() == 1) {
				block_values[bit] = *incoming.begin();
				continue;
			}
			auto it_inserted = phi_wires.insert({bit.wire, block_index});
			if (it_inserted.second) {
				string phi_name = stringf("$phi%d%s", block_index, bit.wire->name.c_str());
				it_inserted.first->second = module->addWire(phi_name, bit.wire->width);
			}
			RTLIL::SigBit phi_bit = {it_inserted.first->second, bit.offset};
			phis[{phi_bit, block_index}] = incoming;
			block_values[bit] = {phi_bit, block_index};
		}
	}
#ifndef NDEBUG
	// And replace the actions with our SSA values. This is just for debugging.
	for (auto &block_values : values) {
		SharedBasicBlock block = block_values.first;
		if (block_values.first == nullptr) continue;
		dict<RTLIL::SigBit, RTLIL::SigBit> compact_phis, compact_values;
		for (auto &bit_ssa : block_values.second) {
			// Include all phis defined by this block.
			if (phis.count(bit_ssa.second)) {
				if (bit_ssa.second.second == indexes(block))
					compact_phis[bit_ssa.second.first] = State::Sm; // m for mux
				// And omit the bit corresponding to the phi, since it's redundant.
				continue;
			}
			// Omit bits defined to the same value by all predecessors.
			bool all_preds_same = !preds[block].empty();
			for (auto &pred : preds[block])
				if (!(values[pred].count(bit_ssa.first) && values[pred][bit_ssa.first] == bit_ssa.second)) {
					all_preds_same = false;
					break;
				}
			// ... except in the exit block (if there is an explicit one).
			if (all_preds_same && !(block->if0 == nullptr && block->if1 == nullptr)) continue;
			// Include the rest.
			compact_values[bit_ssa.first] = bit_ssa.second.first;
		}
		auto phi_actions = collect_actions(compact_phis);
		auto value_actions = collect_actions(compact_values);
		block->actions.clear();
		block->actions.insert(block->actions.end(), phi_actions.begin(), phi_actions.end());
		block->actions.insert(block->actions.end(), value_actions.begin(), value_actions.end());
	}
#endif
	// Collect muxes driving the phis.
	// Note: this is perhaps the most fragile step of the pass, particularly because the exact
	// shape of the mux trees, combined with downstream optimizations, could influence the result
	// in non-obvious ways.
	dict<SharedBasicBlock, SharedBasicBlock> doms = dominators();
	dict<WireSSA, RTLIL::Wire*> mux_wires;
	// (cond_bit, mux_wire_bit) -> (if0, if1)
	dict<std::pair<RTLIL::SigBit, RTLIL::SigBit>, std::pair<RTLIL::SigBit, RTLIL::SigBit>> mux_bits;
	for (auto &phi_incoming : phis) {
		// Each phi collects the values from an output cone centered on the block that dominates
		// every block with an incoming edge towards the phi. To enumerate paths through the cone,
		// one can repeatedly choose the block that has the greatest reverse postorder index, and
		// consider its immediate dominator; if it is the same as a block of another incoming value,
		// both values can be replaced with a mux. Note that only as many paths as there are values
		// will be considered, since if the immediate dominator is not a predecessor of a block,
		// the incoming value from that block will be a phi.
		SigBitSSA phi = phi_incoming.first;
		log_debug("phi %s %d in block %p\n", log_signal(phi.first), phi.second, indexes[phi.second].get());
		dict<SharedBasicBlock, SigBit> incoming;
		for (auto &bit_index : phi_incoming.second) {
			log_assert(!incoming.count(indexes[bit_index.second]));
			incoming[indexes[bit_index.second]] = bit_index.first;
		}
		while (incoming.size() > 1) {
			log_debug("step\n");
			for (auto &block_bit : incoming)
				log_debug("  from %p(%d) incoming %s\n", block_bit.first.get(), indexes(block_bit.first), log_signal(block_bit.second));
			// Find the incoming value we're going to step.
			auto it = std::max_element(incoming.begin(), incoming.end(),
				[&](const std::pair<SharedBasicBlock, SigBit> &a, const std::pair<SharedBasicBlock, SigBit> &b) {
					return indexes(a.first) < indexes(b.first);
				});
			SharedBasicBlock step_block = it->first;
			SigBit step_bit = it->second;
			log_debug("choose block %p\n", step_block.get());
			incoming.erase(it);
			// Merge this incoming value with the incoming value from its immediate dominator, if any.
			SharedBasicBlock idom = doms[step_block];
			log_assert(idom != nullptr);
			if (!incoming.count(idom))
				incoming[idom] = step_bit;
			else {
				auto it_inserted = mux_wires.insert({phi.first.wire, indexes.at(idom)});
				if (it_inserted.second) {
					string mux_name = stringf("$mux%d%s", indexes.at(idom), phi.first.wire->name.c_str());
					it_inserted.first->second = module->addWire(mux_name, phi.first.wire->width);
				}
				RTLIL::SigBit mux_bit = {it_inserted.first->second, phi.first.offset};
				// FIXME: explain
				log_assert(!mux_bits.count({idom->cond, mux_bit}));
				mux_bits[{idom->cond, mux_bit}] = {step_bit, incoming[idom]};
				incoming[idom] = mux_bit;
			}
		}
		module->connect(phi.first, incoming.begin()->second);
	}
	// Create collected muxes. This is a separate step only so that we emit coarse cells.
	std::vector<RTLIL::Cell*> mux_cells;
	mux_bits.sort();
	for (auto &mux_config : mux_bits) {
		RTLIL::SigBit cond_bit, mux_wire_bit, if0_bit, if1_bit;
		std::tie(cond_bit, mux_wire_bit) = mux_config.first;
		std::tie(if0_bit, if1_bit) = mux_config.second;
		if (mux_cells.empty())
			mux_cells.push_back(module->addMux(NEW_ID, if0_bit, if1_bit, cond_bit, mux_wire_bit));
		else if (mux_cells.back()->getPort("\\S") != cond_bit ||
		         mux_cells.back()->getPort("\\Y")[0].wire != mux_wire_bit.wire)
			mux_cells.push_back(module->addMux(NEW_ID, if0_bit, if1_bit, cond_bit, mux_wire_bit));
		else {
			RTLIL::Cell *mux_cell = mux_cells.back();
			mux_cell->parameters["\\WIDTH"] = mux_cell->parameters["\\WIDTH"].as_int() + 1;
			mux_cell->setPort("\\A", {if0_bit, mux_cell->getPort("\\A")});
			mux_cell->setPort("\\B", {if1_bit, mux_cell->getPort("\\B")});
			mux_cell->setPort("\\Y", {mux_wire_bit, mux_cell->getPort("\\Y")});
		}
	}
	// And finally, connect our primary outputs to the phis, by looking at the exit block.
	for (auto &bit_ssa : values[nullptr]) {
		module->connect(bit_ssa.first, bit_ssa.second.first);
	}
}

struct ProcMatchWorker
{
	bool debug_ir = false;

	RTLIL::Module *module;
	SigMap sigmap;

	ProcMatchWorker(RTLIL::Module *mod) : module(mod), sigmap(mod) {}

	SharedBasicBlock build_block_for_compare(RTLIL::SigSpec sig, std::vector<std::pair<RTLIL::SigSpec, SharedBasicBlock>> pats,
	                                         SharedBasicBlock cont)
	{
	entry:
		// The following clauses refer to "Optimizing Pattern Matching" section 3.3 Classical scheme.
		// "Clause 0": no rows
		if (pats.empty())
			return cont;

		// Clause 1: no columns
		if (sig.empty())
			return pats.begin()->second;

		int column = sig.size() - 1;
		bool all_vars = true, all_consts = true;
		auto it = pats.begin();
		for (; it != pats.end(); ++it) {
			RTLIL::State bit = it->first[column].data;
			if (all_vars && bit == State::Sa)
				all_consts = false;
			else if (all_consts && (bit == State::S0 || bit == State::S1))
				all_vars = false;
			else {
				log_assert(bit == State::Sa || bit == State::S0 || bit == State::S1);
				// Neither 2(a) nor 2(b) will apply if we proceed further, so cut the matrix here.
				break;
			}
		}

		if (it != pats.end()) {
			// Clause 2(d): mixture
			RTLIL::SigSpec cut_sig = sig;
			std::vector<std::pair<RTLIL::SigSpec, SharedBasicBlock>> cut_pats;
			while (it != pats.end()) {
				cut_pats.push_back(*it);
				it = pats.erase(it);
			}
			// recurse to build C(x,P₂→L₂)
			cont = build_block_for_compare(cut_sig, cut_pats, cont);
			// and continue building C(x,P₁→L₁)
		}

		log_assert(all_vars || all_consts);
		if (all_vars) {
			// Clause 2(a): all variables
			sig.remove(column);
			std::vector<std::pair<RTLIL::SigSpec, SharedBasicBlock>> patsx;
			for (auto &pat : pats) {
				pat.first.remove(column);
				patsx.push_back(pat);
			}
			pats = patsx;
			goto entry;
		} else /*if (all_consts)*/ {
			// Clause 2(b): all constructors
			RTLIL::SigBit cond = sig[column];
			sig.remove(column);
			std::vector<std::pair<RTLIL::SigSpec, SharedBasicBlock>> pats0, pats1;
			for (auto &pat : pats) {
				RTLIL::State bit = pat.first[column].data;
				pat.first.remove(column);
				if (bit == RTLIL::State::S0)
					pats0.push_back(pat);
				if (bit == RTLIL::State::S1)
					pats1.push_back(pat);
			}

			auto block = std::make_shared<BasicBlock>();
			block->cond = cond;
			block->if0 = build_block_for_compare(sig, pats0, cont);
			block->if1 = build_block_for_compare(sig, pats1, cont);
			return block;
		}
	}

	SharedBasicBlock build_block_for_case(RTLIL::CaseRule *cs, SharedBasicBlock cont)
	{
		for (auto sw_it = cs->switches.rbegin(); sw_it != cs->switches.rend(); ++sw_it)
			cont = build_block_for_switch(*sw_it, cont);

		if (cs->actions.empty())
			return cont;

		auto block = std::make_shared<BasicBlock>();
		block->actions = std::move(cs->actions);
		block->if0 = block->if1 = cont;
		return block;
	}

	SharedBasicBlock build_block_for_switch(RTLIL::SwitchRule *sw, SharedBasicBlock cont)
	{
		std::vector<std::pair<RTLIL::SigSpec, SharedBasicBlock>> pats;
		for (auto &cs : sw->cases) {
			auto block = build_block_for_case(cs, cont);
			if (cs->compare.empty()) {
				cont = block;
				break;
			}
			for (auto &pat : cs->compare)
				pats.push_back({pat, block});
		}
		return build_block_for_compare(sigmap(sw->signal), pats, cont);
	}

	void do_process(RTLIL::IdString id, RTLIL::Process *proc)
	{
		static int debug_num;

		log_debug("Building process IR for %s...\n", log_id(id));
		SharedBasicBlock exit = std::make_shared<BasicBlock>();
		FlowGraph graph = { id.str(), build_block_for_case(&proc->root_case, /*cont=*/exit) };
		log_debug("  Built initial IR graph with %zu blocks.\n", graph.order());
		if (debug_ir) {
			graph.dump_graphviz(stringf("ir-%d-initial.dot", debug_num));
			log_debug("    Dumped IR graph to `ir-%d-initial.dot`.\n", debug_num);
		}
		graph.deduplicate();
		log_debug("  Deduplicated IR graph to %zu blocks.\n", graph.order());
		if (debug_ir) {
			graph.dump_graphviz(stringf("ir-%d-dedup.dot", debug_num));
			log_debug("    Dumped IR graph to `ir-%d-dedup.dot`.\n", debug_num);
		}
		graph.fold_decisions();
		log_debug("  Folded decisions in IR graph.\n");
		if (debug_ir) {
			graph.dump_graphviz(stringf("ir-%d-fold.dot", debug_num));
			log_debug("    Dumped IR graph to `ir-%d-fold.dot`.\n", debug_num);
		}
		graph.cleanup();
		log_debug("  Cleaned IR graph to %zu blocks.\n", graph.order());
		if (debug_ir) {
			graph.dump_graphviz(stringf("ir-%d-clean1.dot", debug_num));
			log_debug("    Dumped IR graph to `ir-%d-clean1.dot`.\n", debug_num);
		}
		graph.sink_assigns();
		log_debug("  Sunk assigns in IR graph.\n");
		if (debug_ir) {
			graph.dump_graphviz(stringf("ir-%d-sink.dot", debug_num));
			log_debug("    Dumped IR graph to `ir-%d-sink.dot`.\n", debug_num);
		}
		graph.cleanup();
		log_debug("  Cleaned IR graph to %zu blocks.\n", graph.order());
		if (debug_ir) {
			graph.dump_graphviz(stringf("ir-%d-clean2.dot", debug_num));
			log_debug("    Dumped IR graph to `ir-%d-clean2.dot`.\n", debug_num);
		}
		std::vector<FlowGraph> subgraphs = graph.split_independent();
		log_debug("  Split IR graph to %zu independent subgraphs.\n", subgraphs.size());
		for (size_t cut = 0; cut < subgraphs.size(); cut++) {
			log_debug("  Processing subgraph %zu:\n", cut);
			FlowGraph &subgraph = subgraphs[cut];
			log_debug("    Cut IR subgraph with %zu blocks.\n", subgraph.order());
			if (debug_ir) {
				subgraph.dump_graphviz(stringf("ir-%d-sub-%zu-initial.dot", debug_num, cut));
				log_debug("      Dumped IR subgraph to `ir-%d-sub-%zu-initial.dot`.\n", debug_num, cut);
			}
			subgraph.hoist_assigns();
			log_debug("    Hoisted assigns in IR subgraph.\n");
			if (debug_ir) {
				subgraph.dump_graphviz(stringf("ir-%d-sub-%zu-hoist.dot", debug_num, cut));
				log_debug("      Dumped IR subgraph to `ir-%d-sub-%zu-hoist.dot`.\n", debug_num, cut);
			}
			subgraph.deduplicate();
			log_debug("    Deduplicated IR subgraph to %zu nodes.\n", subgraph.order());
			if (debug_ir) {
				subgraph.dump_graphviz(stringf("ir-%d-sub-%zu-dedup.dot", debug_num, cut));
				log_debug("      Dumped IR subgraph to `ir-%d-sub-%zu-dedup.dot`.\n", debug_num, cut);
			}
			subgraph.insert_phis(module);
			log_debug("    Inserted PHIs in IR subgraph.\n");
			if (debug_ir) {
				subgraph.dump_graphviz(stringf("ir-%d-sub-%zu-phis.dot", debug_num, cut));
				log_debug("      Dumped IR subgraph to `ir-%d-sub-%zu-phis.dot`.\n", debug_num, cut);
			}
		}

		debug_num++;
	}
};

struct ProcMatchPass : public Pass {
	ProcMatchPass() : Pass("proc_match", "convert decision trees to multiplexers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_match [options] [selection]\n");
		log("\n");
		log("This pass converts the decision trees in processes (originating from if-else\n");
		log("and case statements) to trees of multiplexer cells, using a secondary internal\n");
		log("representation to optimize logic driving multiplexer select signals.\n");
		log("\n");
		log("    -optdelay\n");
		log("        Minimize the delay of logic derived for each multiplexer select signal,\n");
		log("        at the expense of total area. Inverse of -optarea. Default.\n");
		log("\n");
		log("    -optarea\n");
		log("        Minimize the total area of logic derived for all multiplexer select\n");
		log("        signals, at the expense of delay. Inverse of -optdelay.\n");
		log("\n");
		log("    -debug-ir\n");
		log("        Dump the internal representation at various optimization stages.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool optarea = false, optdelay = false, debug_ir = false;

		log_header(design, "Executing PROC_MATCH pass (convert decision trees to multiplexers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-optdelay") {
				optdelay = true;
				continue;
			}
			if (args[argidx] == "-optarea") {
				optarea = true;
				continue;
			}
			if (args[argidx] == "-debug-ir") {
				debug_ir = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (optdelay && optarea)
			log_error("Options -optdelay and -optarea are mutually exclusive!\n");
		if (!(optdelay && optarea))
			optdelay = true;

		for (auto mod : design->modules())
			if (design->selected(mod))
				for (auto &proc_it : mod->processes)
				{
					ProcMatchWorker worker(mod);
					worker.debug_ir = debug_ir;
					if (design->selected(mod, proc_it.second))
						worker.do_process(proc_it.first, proc_it.second);
				}
	}
} ProcMatchPass;

PRIVATE_NAMESPACE_END
