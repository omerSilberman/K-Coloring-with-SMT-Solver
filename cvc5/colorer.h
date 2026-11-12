// The base class of every cvc5 encoding.
#pragma once

#include <cvc5/cvc5.h>  // Native cvc5 API

#include "../common/colorer.h"

// An encoding builds its problem with tm and solver: one term per node in node_vars,
// restricted to K colors in build_variables_and_bounds(), and edge_constraint(u, v),
// u != v unless overridden. An encoding with explicit colors also fills `colors` (the K
// color terms, in build_variables_and_bounds) and returns true from supports_colors(), so
// strategies can fix a node's color; encodings whose colors are not terms of the node's
// sort override fix_color / color_value instead.
class Cvc5Colorer : public GraphColorer {
protected:
    cvc5::TermManager tm;  // cvc5 requires a TermManager
    cvc5::Solver solver;   // native cvc5 solver
    vector<cvc5::Term> node_vars;
    vector<cvc5::Term> colors;  // the K color terms, for strategies (if supports_colors())

public:
    Cvc5Colorer(int k, bool model, bool print) : GraphColorer(k, model, print), solver(tm) {
        if (produce_model) {
            solver.setOption("produce-models", "true");
        }
        solver.setOption("dag-thresh", "0");
    }

protected:
    void set_solver_option(const string& name, const string& value) override {
        solver.setOption(name, value);
    }
    void graph_loaded() override { node_vars.resize(num_nodes + 1); }

    size_t num_assertions() override { return solver.getAssertions().size(); }
    void fix_color(int node, int color) override {
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[node], colors.at(color)}));
    }
    string color_value(int color) override { return solver.getValue(colors.at(color)).toString(); }

    vector<string> assertions_as_text() override {
        vector<string> out;
        for (const auto& formula : solver.getAssertions()) out.push_back(formula.toString());
        return out;
    }

    Result check() override {
        cvc5::Result res = solver.checkSat();
        if (res.isSat()) return Result::Sat;
        if (res.isUnsat()) return Result::Unsat;
        return Result::Unknown;
    }

    void print_model() override {
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

    void add_edge_constraints() override {
        for (const auto& edge : edges) {
            cvc5::Term constraint = edge_constraint_between(edge.first, edge.second);
            if (!constraint.isNull()) {
                solver.assertFormula(constraint);
            }
        }
    }
};
