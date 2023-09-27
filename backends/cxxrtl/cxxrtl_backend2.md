// # CXXRTL2 Archictectural Overview
//
// The goal of the CXXRTL2 backend is to convert a data flow graph represented by an RTLIL netlist
// into a control flow graph in the form of C++ code through a combination of static (compile-time)
// and dynamic (run-time) scheduling, ensuring that the smallest amount of work is performed when
// advancing the simulation or introspecting design state.
//
// CXXRTL2's dynamic scheduling is loosely based on VHDL's simulation semantics, where correctness
// of the concurrent simulation is preserved by splitting each simulation cycle (delta cycle) into
// two phases: eval and commit. In absence of combinatorial loops, the order in which the actions
// are scheduled in the eval phase only affects performance (the amount of delta cycles required for
// convergence); given the same initial state and stimulus, the design will always converge to
// the same subsequent state.
//
// The CXXRTL2 backend is comprised of several analysis steps, described below.
//
// ## Work graph construction
//
// The basic unit in which CXXRTL2 operates is the "work item". Most work items directly correspond
// to RTLIL cells such as $add, $mux, etc., which in turn directly correspond to CXXRTL runtime
// functions such as add_uu<>() or C++ constructs such as if/else. In terms of work items, the goal
// of CXXRTL2 is to convert them to C++ code implementing the eval phase with:
//   (a) an order that minimizes the amount of delta cycles required for convergence;
//   (b) a nesting of scopes that minimizes the amount of work performed per delta cycle, i.e.
//       avoiding computing values that are then thrown out;
//   (c) a respect of C++ compiler implementation limits (maximum expression depth, scope depth, etc.)
//
// Work items have inputs (values required by the computation represented by the work item), outputs
// (values computed by the same), and triggers (values that require the work item to be recomputed).
//
// ## Work graph partitioning
//
// Although it is possible to represent the output of each work item as a C++ variable and
// the scheduled work items as a linear sequence of mostly function calls in the implementation of
// the eval phase, such approach results in very inefficient generated code.
