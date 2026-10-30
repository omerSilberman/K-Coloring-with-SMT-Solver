// The engine-independent part of every encoding: the graph, K, the command-line flags,
// and the run/print protocol. Each engine (cvc5/, z3/) derives its own base class from
// GraphColorer and implements the solver hooks; the encodings derive from that.
#pragma once

#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "graph.h"

using namespace std;

// solve() runs, in this order:
//   set_solver_option()           each --opt NAME=VALUE (before the encoding's own setup,
//                                 so options an encoding requires still win)
//   configure_theory()            the logic and any options the encoding needs
//   build_variables_and_bounds()  one term per node, restricted to K colors
//   add_edge_constraints()        one constraint per edge
// and then prints SAT/UNSAT/UNKNOWN and, with --model, "MODEL: node_1: ... node_2: ...",
// the format benchmark.py and the GUI read. With --print-asserts it first prints every
// assertion on its own "(assert ...)" line.
class GraphColorer {
protected:
    int num_nodes = 0;
    int num_edges = 0;
    int K;
    bool produce_model;
    bool print_asserts;

    vector<pair<int, int>> edges;
    vector<pair<string, string>> solver_options;  // from --opt NAME=VALUE

public:
    GraphColorer(int k, bool model, bool print) : K(k), produce_model(model), print_asserts(print) {}
    virtual ~GraphColorer() = default;

    void load_dimacs(const string& filename) {
        Graph graph = read_dimacs(filename);
        num_nodes = graph.num_nodes;
        num_edges = graph.num_edges;
        edges = std::move(graph.edges);
        graph_loaded();
    }

    // Solver options to set before the encoding configures the solver
    void set_solver_options(const vector<pair<string, string>>& options) { solver_options = options; }

    void solve() {
        for (const auto& [name, value] : solver_options) {
            set_solver_option(name, value);
        }
        configure_theory();
        build_variables_and_bounds();
        add_edge_constraints();

        if (print_asserts) {
            cout << "; --- ASSERTED FORMULAS ---" << endl;
            for (const auto& formula : assertions_as_text()) {
                cout << "(assert " << formula << ")" << endl;
            }
            cout << "; -------------------------" << endl;
        }

        switch (check()) {
        case Result::Sat:
            cout << "SAT" << endl;
            if (produce_model) {
                cout << "MODEL: ";
                print_model();
                cout << endl;
            }
            break;
        case Result::Unsat:
            cout << "UNSAT" << endl;
            break;
        case Result::Unknown:
            cout << "UNKNOWN" << endl;
            break;
        }
    }

protected:
    enum class Result { Sat, Unsat, Unknown };

    // --- implemented once per engine ---
    virtual void set_solver_option(const string& name, const string& value) = 0;
    virtual void graph_loaded() {}                    // e.g. size node_vars
    virtual void add_edge_constraints() = 0;
    virtual vector<string> assertions_as_text() = 0;  // one string per assertion, one line each
    virtual Result check() = 0;
    virtual void print_model() = 0;                   // "node_i: <value> " for every node

    // --- implemented by every encoding ---
    virtual void configure_theory() = 0;
    virtual void build_variables_and_bounds() = 0;
};
