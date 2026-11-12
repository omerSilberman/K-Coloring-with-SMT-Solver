// The engine-independent part of every encoding: the graph, K, the command-line flags,
// the strategies, and the run/print protocol. Each engine (cvc5/, z3/) derives its own base
// class from GraphColorer and implements the solver hooks; the encodings derive from that.
#pragma once

#include <iostream>
#include <memory>
#include <regex>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "graph.h"
#include "json.h"
#include "strategies/strategy.h"

using namespace std;

// solve() runs, in this order:
//   the strategies (--strategy), which may answer right away or shrink the graph
//   set_solver_option()           each --opt NAME=VALUE (before the encoding's own setup,
//                                 so options an encoding requires still win)
//   configure_theory()            the logic and any options the encoding needs
//   build_variables_and_bounds()  one term per node, restricted to K colors
//   add_edge_constraints()        one constraint per edge
//   fix_color()                   the colors the strategies fixed (e.g. a clique's)
// and then prints SAT/UNSAT/UNKNOWN and, with --model, "MODEL: node_1: ... node_2: ...",
// the format benchmark.py and the GUI read. With --print-asserts it first prints every
// assertion on its own "(assert ...)" line. With strategies, each one first prints a
// "STRATEGY name: ..." line and a "STRATEGY-JSON {...}" line, and the model is for the
// original graph (removed nodes repaired).
class GraphColorer {
protected:
    int num_nodes = 0;
    int num_edges = 0;
    int K;
    bool produce_model;
    bool print_asserts;

    vector<pair<int, int>> edges;
    vector<pair<string, string>> solver_options;  // from --opt NAME=VALUE
    vector<string> strategy_specs;                // from --strategy NAME[:PARAMS]

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
    void set_strategies(const vector<string>& specs) { strategy_specs = specs; }

    // Whether the encoding has explicit colors, so a strategy can fix a node's color (and
    // repair removed nodes). Encodings that do also implement fix_color / color_value.
    virtual bool supports_colors() const { return false; }

    void solve() {
        strategies::Plan plan;
        bool with_strategies = !strategy_specs.empty();
        if (with_strategies) {
            plan = strategies::run_strategies({num_nodes, num_edges, edges}, strategy_specs, {K, supports_colors()});
            print_reports(plan);
            if (plan.decided) {
                print_decided(plan);
                return;
            }
            num_nodes = plan.graph.num_nodes;
            num_edges = plan.graph.num_edges;
            edges = plan.graph.edges;
            graph_loaded();
        }

        for (const auto& [name, value] : solver_options) {
            set_solver_option(name, value);
        }
        configure_theory();
        build_variables_and_bounds();
        add_edge_constraints();
        size_t before_fixes = with_strategies ? num_assertions() : 0;
        for (const auto& [node, color] : plan.fixed) fix_color(node, color);

        if (print_asserts) {
            cout << "; --- ASSERTED FORMULAS ---" << endl;
            vector<string> formulas = assertions_as_text();
            for (size_t i = 0; i < formulas.size(); i++) {
                // the strategies' assertions come last, marked for the GUI
                if (with_strategies && i == before_fixes) cout << "; strategy: clique" << endl;
                cout << "(assert " << formulas[i] << ")" << endl;
            }
            cout << "; -------------------------" << endl;
        }

        switch (check()) {
        case Result::Sat:
            cout << "SAT" << endl;
            if (produce_model) {
                cout << "MODEL: ";
                if (with_strategies) print_repaired_model(plan);
                else print_model();
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
    virtual size_t num_assertions() = 0;
    virtual Result check() = 0;
    virtual void print_model() = 0;                   // "node_i: <value> " for every node
    // Node `node` has color `color` (0..K-1), and that color's value as print_model prints
    // it, after a SAT check. Only called when supports_colors().
    virtual void fix_color(int node, int color) = 0;
    virtual string color_value(int color) = 0;

    // Encodings build their color terms only when strategies run: creating terms, even
    // unused ones, changes a solver's internal order and so its search and its models
    bool strategies_given() const { return !strategy_specs.empty(); }

    // --- implemented by every encoding ---
    virtual void configure_theory() = 0;
    virtual void build_variables_and_bounds() = 0;

private:
    static void print_reports(const strategies::Plan& plan) {
        for (const auto& r : plan.reports) {
            ostringstream ms;
            ms.precision(3);
            ms << r.ms;
            cout << "STRATEGY " << r.name << ": " << r.text << " (" << ms.str() << " ms)" << endl;
            string fixed = "[";
            for (size_t i = 0; i < r.fixed.size(); i++) {
                fixed += (i ? "," : "") + string("[") + to_string(r.fixed[i].first) + "," + to_string(r.fixed[i].second) + "]";
            }
            fixed += "]";
            cout << "STRATEGY-JSON {\"name\":" << json_string(r.name) << ",\"text\":" << json_string(r.text)
                 << ",\"ms\":" << ms.str() << ",\"decided\":" << (r.decided ? "true" : "false")
                 << ",\"removed\":" << json_ints(r.removed) << ",\"fixed\":" << fixed
                 << ",\"clique\":" << json_ints(r.clique) << "}" << endl;
        }
    }

    // An answer found without the solver; a SAT model numbers the colors 1..K
    void print_decided(const strategies::Plan& plan) {
        if (!*plan.decided) {
            cout << "UNSAT" << endl;
            return;
        }
        cout << "SAT" << endl;
        if (produce_model) {
            cout << "MODEL: ";
            for (int v = 1; v <= plan.original_nodes; v++) {
                cout << "node_" << v << ": " << plan.decided_colors[v] + 1 << " ";
            }
            cout << endl;
        }
    }

    // The model of the reduced graph, mapped back to the original node numbers, with the
    // removed nodes repaired (in reverse order of removal)
    void print_repaired_model(const strategies::Plan& plan) {
        // what the encoding prints, split into "name: value" pairs
        ostringstream captured;
        streambuf* old = cout.rdbuf(captured.rdbuf());
        print_model();
        cout.rdbuf(old);
        string text = captured.str();
        vector<pair<string, string>> pairs;
        regex key(R"((?:^|\s)([^\s:]+): )");
        vector<pair<size_t, size_t>> keys;  // (start of name, start of value)
        vector<string> names;
        for (auto it = sregex_iterator(text.begin(), text.end(), key); it != sregex_iterator(); ++it) {
            keys.push_back({(size_t)it->position(1), (size_t)(it->position(0) + it->length(0))});
            names.push_back((*it)[1]);
        }
        for (size_t i = 0; i < keys.size(); i++) {
            size_t end = i + 1 < keys.size() ? keys[i + 1].first : text.size();
            string value = text.substr(keys[i].second, end - keys[i].second);
            value.erase(value.find_last_not_of(" \n") + 1);
            pairs.push_back({names[i], value});
        }

        vector<string> color(plan.original_nodes + 1);
        vector<pair<string, string>> extra;
        regex node_name(R"(node_(\d+))");
        smatch m;
        for (const auto& [name, value] : pairs) {
            if (regex_match(name, m, node_name)) {
                int v = stoi(m[1]);
                if (v >= 1 && v < (int)plan.original.size()) color[plan.original[v]] = value;
            } else {
                extra.push_back({name, value});
            }
        }
        vector<string> palette;  // the K colors as printed, computed when first needed
        for (auto it = plan.repairs.rbegin(); it != plan.repairs.rend(); ++it) {
            if (it->kind == strategies::Repair::Kind::CopyColor) {
                color[it->node] = color[it->source];
                continue;
            }
            if (palette.empty()) {
                for (int c = 0; c < K; c++) palette.push_back(color_value(c));
            }
            for (const auto& candidate : palette) {
                bool taken = false;
                for (int w : it->neighbours) taken = taken || color[w] == candidate;
                if (!taken) {
                    color[it->node] = candidate;
                    break;
                }
            }
        }
        for (int v = 1; v <= plan.original_nodes; v++) cout << "node_" << v << ": " << color[v] << " ";
        // auxiliary values (i_1_3, idx_3, word) refer to the reduced graph's numbering, so
        // they are kept only if no node was removed
        if (plan.graph.num_nodes == plan.original_nodes) {
            for (const auto& [name, value] : extra) cout << name << ": " << value << " ";
        }
    }
};
