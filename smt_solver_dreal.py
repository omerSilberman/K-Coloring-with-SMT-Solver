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
    ./smt_solver_dreal.py <THEORY> <dimacs_file> <K> [--model] [--print-asserts] [--precision D] [--jobs N]
"""
import ctypes
import os
import signal
import subprocess
import sys

PI = "3.141592653589793"
DEFAULT_JOBS = 8

# dReal 4.21.06.2 and its libraries unpacked from .deb files (see README, "dReal").
DREAL_ROOT = os.environ.get("DREAL_ROOT", os.path.expanduser("~/dreal/root"))
DREAL_BIN = os.path.join(DREAL_ROOT, "opt/dreal/4.21.06.2/bin/dreal")
DREAL_LIBS = [
    "opt/libibex/2.7.4/lib",
    "opt/dreal/4.21.06.2/lib",
    "usr/lib/x86_64-linux-gnu",
    "usr/lib/x86_64-linux-gnu/blas",
    "usr/lib/x86_64-linux-gnu/lapack",
]

# ============================================================================
# ENCODINGS
# ============================================================================
# Each node is a real x with f(x) = 0. The roots of f are `step` apart starting at `offset`
# (as in smt_solver_cvc5):
#   NLRA-SIN     sin(x)         roots at n*pi          (step pi,   offset 0)
#   NLRA-COS     cos(x)         roots at pi/2 + n*pi   (step pi,   offset pi/2)
#   NLRA-SINCOS  sin(x)*cos(x)  roots at n*pi/2        (step pi/2, offset 0)
#   NLRA-SINPI   sin(pi*x)      roots at n             (step 1,    offset 0)
# with n in [-lo, hi], lo + hi = K - 1. dReal has no exact pi, so pi is a decimal literal.
THEORIES = {
    "NLRA-SIN":    {"f": "(sin {x})",                 "step": 3.141592653589793,     "offset": 0.0},
    "NLRA-COS":    {"f": "(cos {x})",                 "step": 3.141592653589793,     "offset": 1.5707963267948966},
    "NLRA-SINCOS": {"f": "(* (sin {x}) (cos {x}))",   "step": 1.5707963267948966,    "offset": 0.0},
    "NLRA-SINPI":  {"f": f"(sin (* {PI} {{x}}))",     "step": 1.0,                   "offset": 0.0},
}
ROOT_NAMES = {
    "NLRA-SIN":    lambda n: f"{n}*pi",
    "NLRA-COS":    lambda n: f"pi/2{n:+d}*pi",
    "NLRA-SINCOS": lambda n: f"{n}*pi/2",
    "NLRA-SINPI":  lambda n: f"{n}",
}


def load_dimacs(filename):
    num_nodes, edges = 0, []
    with open(filename) as f:
        for line in f:
            if line.startswith("p"):
                num_nodes = int(line.split()[2])
            elif line.startswith("e"):
                _, u, v = line.split()[:3]
                edges.append((int(u), int(v)))
    return num_nodes, edges


def build_query(theory, num_nodes, edges, K):
    enc = THEORIES[theory]
    step, offset = enc["step"], enc["offset"]
    lo = (K - 1) // 2
    hi = (K - 1) - lo
    # The box reaches half a step past the outermost roots, so it holds exactly K roots and
    # none of them sits on its boundary (where the decimal pi and delta would make it fragile).
    lower = offset - (lo + 0.5) * step
    upper = offset + (hi + 0.5) * step

    lines = ["(set-logic QF_NRA)"]
    for i in range(1, num_nodes + 1):
        lines.append(f"(declare-fun node_{i} () Real)")
    for i in range(1, num_nodes + 1):
        x = f"node_{i}"
        lines.append(f"(assert (>= {x} {lower!r}))")
        lines.append(f"(assert (<= {x} {upper!r}))")
        lines.append(f"(assert (= {enc['f'].format(x=x)} 0))")
    # Not (not (= u v)): delta-weakening turns u != v into something u = v satisfies.
    # Distinct roots are a full step apart, so ask for half a step instead.
    sep = step / 2
    for u, v in edges:
        lines.append(f"(assert (>= (abs (- node_{u} node_{v})) {sep!r}))")
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n"


def kill_with_parent():
    # Runs in the dReal child: if this script is killed (benchmark.py's timeout), so is dReal.
    PR_SET_PDEATHSIG = 1
    ctypes.CDLL("libc.so.6", use_errno=True).prctl(PR_SET_PDEATHSIG, signal.SIGKILL)


def run_dreal(query, precision, jobs):
    env = dict(os.environ)
    libs = [os.path.join(DREAL_ROOT, p) for p in DREAL_LIBS]
    env["LD_LIBRARY_PATH"] = ":".join(libs + [env.get("LD_LIBRARY_PATH", "")]).rstrip(":")
    cmd = [DREAL_BIN, "--in", "--model", "--precision", str(precision), "--jobs", str(jobs)]
    result = subprocess.run(cmd, input=query, capture_output=True, text=True, env=env,
                            preexec_fn=kill_with_parent)
    return result.stdout, result.stderr


def parse_boxes(output):
    """`node_3 : [3.1415926535897931, 3.1415926535897936]` -> {3: (lo, hi)}."""
    boxes = {}
    for line in output.splitlines():
        if line.startswith("node_") and ":" in line:
            name, interval = line.split(":", 1)
            a, b = interval.strip().strip("[]").split(",")
            boxes[int(name.strip()[len("node_"):])] = (float(a), float(b))
    return boxes


def round_to_roots(theory, boxes, num_nodes, edges, K):
    """Root index n for every node, or an error message if the boxes are not a K-coloring."""
    enc = THEORIES[theory]
    step, offset = enc["step"], enc["offset"]
    lo = (K - 1) // 2
    hi = (K - 1) - lo
    color = {}
    for i in range(1, num_nodes + 1):
        if i not in boxes:
            return None, f"no value for node_{i}"
        mid = sum(boxes[i]) / 2
        n = round((mid - offset) / step)
        if abs(mid - (offset + n * step)) > step / 4:
            return None, f"node_{i} = {mid} is not near a root"
        if not -lo <= n <= hi:
            return None, f"node_{i} rounds to root {n}, outside [-{lo}, {hi}]"
        color[i] = n
    for u, v in edges:
        if color[u] == color[v]:
            return None, f"edge {u}-{v}: both nodes round to root {color[u]}"
    return color, None


def main():
    args = sys.argv[1:]
    if not args or "--help" in args or "-h" in args:
        print("Usage: ./smt_solver_dreal.py <THEORY> <dimacs_file> <K> [OPTIONS]")
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

    num_nodes, edges = load_dimacs(filename)
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
