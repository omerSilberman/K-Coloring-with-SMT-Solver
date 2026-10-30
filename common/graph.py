"""A graph in DIMACS format, for the Python parts (dReal, the GUI). The C++ engines use
common/graph.h, which reads files the same way."""


def read_dimacs(filename):
    """(num_nodes, edges) from "p edge N M" and "e U V" lines; nodes are numbered 1..N."""
    num_nodes, edges = 0, []
    with open(filename) as f:
        for line in f:
            if line.startswith("p"):
                num_nodes = int(line.split()[2])
            elif line.startswith("e"):
                _, u, v = line.split()[:3]
                edges.append((int(u), int(v)))
    return num_nodes, edges
