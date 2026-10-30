// The base class of every cvc5 encoding.
#pragma once

#include <cvc5/cvc5.h>  // Native cvc5 API

#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "graph.h"

using namespace std;

// An encoding builds one cvc5 problem for "can this graph be colored with K colors?":
//   configure_theory()            the logic and any cvc5 options the encoding needs
//   build_variables_and_bounds()  one term per node in node_vars, restricted to K colors
//   edge constraints              edge_constraint(u, v), u != v unless overridden
// solve() runs these in order, checks satisfiability and prints SAT/UNSAT/UNKNOWN and,
// with --model, "MODEL: node_1: ... node_2: ..." (the format benchmark.py and the GUI read).
class AbstractGraphColorer {
protected:
    int num_nodes = 0;
    int num_edges = 0;
    int K;
    bool produce_model;
    bool print_asserts;

    vector<pair<int, int>> edges;
    vector<pair<string, string>> cvc5_options;  // from --opt NAME=VALUE
    cvc5::TermManager tm;  // cvc5 requires a TermManager
    cvc5::Solver solver;   // native cvc5 solver
    vector<cvc5::Term> node_vars;

public:
    AbstractGraphColorer(int k, bool model, bool print)
        : K(k), produce_model(model), print_asserts(print), solver(tm) {
        if (produce_model) {
            solver.setOption("produce-models", "true");
        }
        solver.setOption("dag-thresh", "0");
    }

    virtual ~AbstractGraphColorer() = default;

    void load_dimacs(const string& filename) {
        Graph graph = read_dimacs(filename);
        num_nodes = graph.num_nodes;
        num_edges = graph.num_edges;
        edges = std::move(graph.edges);
        node_vars.resize(num_nodes + 1);
    }

    // cvc5 options to set before the encoding configures the solver
    void set_cvc5_options(const vector<pair<string, string>>& options) { cvc5_options = options; }

    void solve() {
        // Before configure_theory, so options an encoding requires (e.g. SEP's) still win
        for (const auto& [name, value] : cvc5_options) {
            solver.setOption(name, value);
        }
        configure_theory();
        build_variables_and_bounds();
        build_universal_edge_constraints();

        if (print_asserts) {
            cout << "; --- ASSERTED FORMULAS ---" << endl;
            for (const auto& formula : solver.getAssertions()) {
                cout << "(assert " << formula.toString() << ")" << endl;
            }
            cout << "; -------------------------" << endl;
        }

        cvc5::Result res = solver.checkSat();

        if (res.isSat()) {
            cout << "SAT" << endl;
            if (produce_model) {
                cout << "MODEL: ";
                print_model();
                cout << endl;
            }
        } else if (res.isUnsat()) {
            cout << "UNSAT" << endl;
        } else {
            cout << "UNKNOWN" << endl;
        }
    }

protected:
    virtual void configure_theory() = 0;
    virtual void build_variables_and_bounds() = 0;
    virtual void print_model() {
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": " << solver.getValue(node_vars[i]).toString() << " ";
        }
    }
    // The two endpoints of an edge get different colors (u != v unless overridden)
    virtual cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) {
        return tm.mkTerm(cvc5::Kind::NOT, {tm.mkTerm(cvc5::Kind::EQUAL, {u, v})});
    }
    // Override for encodings whose node color is not a single term in node_vars
    // (null term = nothing to assert for this edge)
    virtual cvc5::Term edge_constraint_between(int u, int v) {
        return edge_constraint(node_vars[u], node_vars[v]);
    }

private:
    void build_universal_edge_constraints() {
        for (const auto& edge : edges) {
            cvc5::Term constraint = edge_constraint_between(edge.first, edge.second);
            if (!constraint.isNull()) {
                solver.assertFormula(constraint);
            }
        }
    }
};
