"""The trig encodings for dReal: the SMT-LIB query for each one, and how a delta-sat box
is rounded back to an exact coloring.

Each node is a real x with f(x) = 0. The roots of f are `step` apart starting at `offset`
(as in cvc5/real.cpp):
  NLRA-SIN     sin(x)         roots at n*pi          (step pi,   offset 0)
  NLRA-COS     cos(x)         roots at pi/2 + n*pi   (step pi,   offset pi/2)
  NLRA-SINCOS  sin(x)*cos(x)  roots at n*pi/2        (step pi/2, offset 0)
  NLRA-SINPI   sin(pi*x)      roots at n             (step 1,    offset 0)
with n in [-lo, hi], lo + hi = K - 1. dReal has no exact pi, so pi is a decimal literal.
"""

PI = "3.141592653589793"

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
