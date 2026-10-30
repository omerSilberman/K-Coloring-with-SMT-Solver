#!/usr/bin/env python3
"""K-coloring with the trig encodings of smt_solver_cvc5, solved by dReal (a delta-complete SMT solver).

cvc5 proves the trig encodings UNSAT but never finds a SAT model: the roots of sin/cos
are irrational, and cvc5 only builds exact models. dReal answers either "unsat" (sound,
like cvc5) or "delta-sat": a box around each variable where every constraint holds up
to delta, e.g. node_1 : [3.14159265358979, 3.14159265358980] for sin(x) = 0.

A delta-sat answer is turned into an exact coloring: each node is rounded to the nearest
root, and the coloring is checked against every edge. Only then does this print SAT;
if the check fails it prints UNKNOWN.

Same command line and output as smt_solver_cvc5, so benchmark.py can run both:
    ./dreal/smt_solver_dreal.py <THEORY> <dimacs_file> <K> [--model] [--print-asserts] [--precision D] [--jobs N]

The encodings are in trig_encodings.py, the dReal process in runner.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "common"))

from trig_encodings import ROOT_NAMES, THEORIES, build_query, round_to_roots  # noqa: E402
from graph import read_dimacs  # noqa: E402
from runner import DREAL_BIN, parse_boxes, run_dreal  # noqa: E402

DEFAULT_JOBS = 8


def main():
    args = sys.argv[1:]
    if not args or "--help" in args or "-h" in args:
        print("Usage: ./dreal/smt_solver_dreal.py <THEORY> <dimacs_file> <K> [OPTIONS]")
        print("Options:")
        print("  --model          Produce and print the coloring model if SAT")
        print("  --print-asserts  Print the SMT-LIB query sent to dReal before solving")
        print("  --precision D    dReal's delta (default 0.001)")
        print(f"  --jobs N         dReal's parallel search threads (default {DEFAULT_JOBS})")
        print("  --help, -h       Show this help message")
        print("\nAvailable Theories:")
        print("  " + ", ".join(THEORIES))
        return 0

    produce_model = print_asserts = False
    precision = 0.001
    jobs = DEFAULT_JOBS
    pos_args = []
    i = 0
    while i < len(args):
        if args[i] == "--model":
            produce_model = True
        elif args[i] == "--print-asserts":
            print_asserts = True
        elif args[i] == "--precision":
            i += 1
            precision = float(args[i])
        elif args[i] == "--jobs":
            i += 1
            jobs = int(args[i])
        else:
            pos_args.append(args[i])
        i += 1

    if len(pos_args) < 3:
        print("Error: Missing required arguments. Use --help for more information.", file=sys.stderr)
        return 1
    theory, filename = pos_args[0], pos_args[1]
    try:
        K = int(pos_args[2])
    except ValueError:
        print("Error: K must be an integer.", file=sys.stderr)
        return 1
    if theory not in THEORIES:
        print(f"Error: Unknown theory '{theory}'.", file=sys.stderr)
        return 1
    if not os.path.exists(DREAL_BIN):
        print(f"Error: dReal not found at {DREAL_BIN} (set DREAL_ROOT).", file=sys.stderr)
        return 1

    num_nodes, edges = read_dimacs(filename)
    query = build_query(theory, num_nodes, edges, K)
    if print_asserts:
        print("; --- QUERY SENT TO DREAL ---")
        print(query, end="")
        print("; ---------------------------")

    output, errors = run_dreal(query, precision, jobs)
    first = output.strip().splitlines()[0] if output.strip() else ""

    if first == "unsat":
        print("UNSAT")
    elif first.startswith("delta-sat"):
        color, problem = round_to_roots(theory, parse_boxes(output), num_nodes, edges, K)
        if color is None:
            print(f"dReal returned {first}, but rounding failed: {problem}", file=sys.stderr)
            print("UNKNOWN")
        else:
            print("SAT")
            if produce_model:
                name = ROOT_NAMES[theory]
                print("MODEL: " + " ".join(f"node_{i}: {name(color[i])}" for i in range(1, num_nodes + 1)))
    else:
        print(f"Unexpected dReal output: {output.strip()} {errors.strip()}", file=sys.stderr)
        print("UNKNOWN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
