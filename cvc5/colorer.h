// The base class of every cvc5 encoding.
#pragma once

#include <cvc5/cvc5.h>  // Native cvc5 API

#include <functional>
#include <sstream>
#include <unordered_set>

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
    // What --dump-smt2 must repeat that the assertions do not show
    vector<pair<string, string>> options_set;
    vector<pair<cvc5::Sort, cvc5::Sort>> sep_heaps;

public:
    Cvc5Colorer(int k, bool model, bool print) : GraphColorer(k, model, print), solver(tm) {
        if (produce_model) {
            solver.setOption("produce-models", "true");
        }
        solver.setOption("dag-thresh", "0");
    }

protected:
    void set_solver_option(const string& name, const string& value) override { set_option(name, value); }
    // Encodings set options and declare the separation-logic heap through these, so that
    // --dump-smt2 writes them into the benchmark too
    void set_option(const string& name, const string& value) {
        solver.setOption(name, value);
        options_set.push_back({name, value});
    }
    void declare_sep_heap(const cvc5::Sort& location, const cvc5::Sort& data) {
        solver.declareSepHeap(location, data);
        sep_heaps.push_back({location, data});
    }

    // cvc5 has no call that prints a whole benchmark, so the declarations are rebuilt from
    // the assertions: every free symbol, uninterpreted sort and datatype they use.
    // Written straight to out: the benchmark can be larger than the solver's own memory use
    void write_smt2(ostream& out, const string& status) override {
        vector<cvc5::Term> assertions = solver.getAssertions();
        vector<cvc5::Term> symbols;      // in first-use order
        vector<cvc5::Sort> sorts;        // uninterpreted sorts
        vector<cvc5::Sort> datatypes;    // each after the datatypes its fields use
        unordered_set<cvc5::Term> seen_terms;
        unordered_set<cvc5::Sort> seen_sorts;

        function<void(const cvc5::Sort&)> add_sort = [&](const cvc5::Sort& s) {
            if (s.isNull() || !seen_sorts.insert(s).second) return;
            vector<cvc5::Sort> parts;
            if (s.isUninterpretedSort()) {
                sorts.push_back(s);
                return;
            } else if (s.isFunction()) {
                parts = s.getFunctionDomainSorts();
                parts.push_back(s.getFunctionCodomainSort());
            } else if (s.isArray()) {
                parts = {s.getArrayIndexSort(), s.getArrayElementSort()};
            } else if (s.isSet()) {
                parts = {s.getSetElementSort()};
            } else if (s.isBag()) {
                parts = {s.getBagElementSort()};
            } else if (s.isSequence()) {
                parts = {s.getSequenceElementSort()};
            } else if (s.isTuple()) {
                parts = s.getTupleSorts();
            } else if (s.isDatatypeConstructor()) {
                parts = s.getDatatypeConstructorDomainSorts();
                parts.push_back(s.getDatatypeConstructorCodomainSort());
            } else if (s.isDatatypeSelector()) {
                parts = {s.getDatatypeSelectorDomainSort(), s.getDatatypeSelectorCodomainSort()};
            } else if (s.isDatatypeTester()) {
                parts = {s.getDatatypeTesterDomainSort()};
            } else if (s.isDatatype()) {
                for (const auto& constructor : s.getDatatype()) {
                    for (const auto& selector : constructor) add_sort(selector.getCodomainSort());
                }
                datatypes.push_back(s);
                return;
            }
            for (const auto& part : parts) add_sort(part);
        };

        vector<cvc5::Term> stack(assertions.rbegin(), assertions.rend());
        while (!stack.empty()) {
            cvc5::Term t = stack.back();
            stack.pop_back();
            if (!seen_terms.insert(t).second) continue;
            add_sort(t.getSort());
            if (t.getKind() == cvc5::Kind::CONSTANT) symbols.push_back(t);
            for (size_t i = t.getNumChildren(); i-- > 0;) stack.push_back(t[i]);
        }

        for (const auto& [name, value] : options_set) out << "(set-option :" << name << " " << value << ")\n";
        if (solver.isLogicSet()) out << "(set-logic " << solver.getLogic() << ")\n";
        out << "(set-info :status " << status << ")\n";
        for (const auto& s : sorts) out << "(declare-sort " << s << " 0)\n";
        for (const auto& s : datatypes) {
            out << "(declare-datatype " << s << " (";
            for (const auto& constructor : s.getDatatype()) {
                out << "(" << smt2_symbol(constructor.getName());
                for (const auto& selector : constructor) {
                    out << " (" << smt2_symbol(selector.getName()) << " " << selector.getCodomainSort() << ")";
                }
                out << ")";
            }
            out << "))\n";
        }
        for (const auto& [location, data] : sep_heaps) out << "(declare-heap (" << location << " " << data << "))\n";
        for (const auto& symbol : symbols) {
            cvc5::Sort s = symbol.getSort();
            out << "(declare-fun " << symbol << " (";
            if (s.isFunction()) {
                vector<cvc5::Sort> domain = s.getFunctionDomainSorts();
                for (size_t i = 0; i < domain.size(); i++) out << (i ? " " : "") << domain[i];
                out << ") " << s.getFunctionCodomainSort() << ")\n";
            } else {
                out << ") " << s << ")\n";
            }
        }
        for (const auto& formula : assertions) out << "(assert " << formula << ")\n";
        out << "(check-sat)\n";
    }

    // A name as an SMT-LIB symbol: as is if it is a simple symbol, else in |...|
    static string smt2_symbol(const string& name) {
        static const string extra = "~!@$%^&*_-+=<>.?/";
        bool simple = !name.empty() && !isdigit((unsigned char)name[0]);
        for (char c : name) simple = simple && (isalnum((unsigned char)c) || extra.find(c) != string::npos);
        return simple ? name : "|" + name + "|";
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
