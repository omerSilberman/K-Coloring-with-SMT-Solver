// A graph in DIMACS format. Nothing here depends on cvc5, so this file can move to a
// shared folder once another solver backend needs it.
#pragma once

#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

struct Graph {
    int num_nodes = 0;
    int num_edges = 0;                          // as declared in the "p" line
    std::vector<std::pair<int, int>> edges;     // nodes are numbered 1..num_nodes
};

// Reads "p edge N M" and "e U V" lines; "c" lines are comments
inline Graph read_dimacs(const std::string& filename) {
    std::ifstream infile(filename);
    if (!infile.is_open()) {
        throw std::runtime_error("Could not open file: " + filename);
    }

    Graph graph;
    std::string line;
    while (std::getline(infile, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            std::string p, edge;
            std::stringstream ss(line);
            ss >> p >> edge >> graph.num_nodes >> graph.num_edges;
        } else if (line[0] == 'e') {
            char e;
            int u, v;
            std::stringstream ss(line);
            ss >> e >> u >> v;
            graph.edges.push_back({u, v});
        }
    }
    return graph;
}
