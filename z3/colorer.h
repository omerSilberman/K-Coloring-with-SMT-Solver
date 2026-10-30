// The base class of every Z3 encoding.
#pragma once

#include <z3++.h>

#include <optional>

#include "../common/colorer.h"

// An encoding builds its problem with ctx and solver: one term per node in node_vars,
// restricted to K colors in build_variables_and_bounds(), and edge_constraint(u, v),
// u != v unless overridden. In configure_theory() it calls set_logic(), since Z3 picks
// its solver (and its tactics) when the solver is created.
class Z3Colorer : public GraphColorer {
protected:
    z3::context ctx;
    z3::solver solver;
    vector<z3::expr> node_vars;
    optional<z3::model> last_model;  // after a SAT check

public:
    Z3Colorer(int k, bool model, bool print) : GraphColorer(k, model, print), solver(ctx) {
        // --print-asserts: one assertion per line, written out in full
        z3::set_param("pp.single_line", true);
        z3::set_param("pp.max_depth", 1000000);
        z3::set_param("pp.min_alias_size", 1000000);
    }

protected:
    // A solver for an SMT-LIB logic ("ALL" = let Z3 choose)
    void set_logic(const string& logic) {
        solver = (logic == "ALL") ? z3::solver(ctx) : z3::solver(ctx, logic.c_str());
    }

    // Z3 options are global parameters (e.g. smt.random_seed, sat.euf); they apply to
    // the solver configure_theory() creates next
    void set_solver_option(const string& name, const string& value) override {
        z3::set_param(name.c_str(), value.c_str());
    }
    void graph_loaded() override { node_vars.assign(num_nodes + 1, ctx.bool_val(false)); }

    vector<string> assertions_as_text() override {
        vector<string> out;
        for (const auto& formula : solver.assertions()) out.push_back(formula.to_string());
        return out;
    }

    Result check() override {
        switch (solver.check()) {
        case z3::sat:
            last_model = solver.get_model();
            return Result::Sat;
        case z3::unsat:
            return Result::Unsat;
        default:
            return Result::Unknown;
        }
    }

    // The value of e in the model (model completion: unconstrained parts get a value too)
    z3::expr value(const z3::expr& e) { return last_model->eval(e, true); }

    void print_model() override {
        for (int i = 1; i <= num_nodes; i++) {
            cout << "node_" << i << ": " << value(node_vars[i]).to_string() << " ";
        }
    }

    // The two endpoints of an edge get different colors (u != v unless overridden)
    virtual z3::expr edge_constraint(const z3::expr& u, const z3::expr& v) { return !(u == v); }
    // Override for encodings whose node color is not a single term in node_vars
    // (nullopt = nothing to assert for this edge)
    virtual optional<z3::expr> edge_constraint_between(int u, int v) {
        return edge_constraint(node_vars[u], node_vars[v]);
    }

    void add_edge_constraints() override {
        for (const auto& edge : edges) {
            optional<z3::expr> constraint = edge_constraint_between(edge.first, edge.second);
            if (constraint) solver.add(*constraint);
        }
    }

    // A fresh constant, like cvc5's mkConst
    z3::expr constant(const string& name, const z3::sort& sort) { return ctx.constant(name.c_str(), sort); }
    // OR / AND / DISTINCT over a vector (a single argument stands alone, as in the cvc5 code)
    z3::expr any_of(const vector<z3::expr>& args) { return args.size() == 1 ? args[0] : z3::mk_or(vec(args)); }
    z3::expr all_of(const vector<z3::expr>& args) { return args.size() == 1 ? args[0] : z3::mk_and(vec(args)); }
    z3::expr all_distinct(const vector<z3::expr>& args) { return z3::distinct(vec(args)); }
    z3::expr_vector vec(const vector<z3::expr>& args) {
        z3::expr_vector out(ctx);
        for (const auto& a : args) out.push_back(a);
        return out;
    }
};
