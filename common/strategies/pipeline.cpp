// The strategy registry and the pipeline that runs them.
#include <algorithm>
#include <chrono>
#include <sstream>

#include "graph_tools.h"

namespace strategies {

namespace {

struct Entry {
    StrategyInfo info;
    std::unique_ptr<Strategy> (*make)(const Params&);
};

const std::vector<Entry>& entries() {
    static const std::vector<Entry> list = {
        {{"dsatur", 0, "pre-check", false,
          "Color the graph with the DSATUR heuristic; if that needs at most K colors, the answer is SAT without the solver.", ""},
         make_dsatur},
        {{"dominated", 1, "reduction", false,
          "Remove every node whose neighbours are all neighbours of another, non-adjacent node; it copies that node's color afterwards.",
          "ms=N (time budget, default 2000)"},
         make_dominated},
        {{"peel", 2, "reduction", true,
          "Repeatedly remove nodes with fewer than K neighbours; each gets a color its neighbours do not have afterwards.", ""},
         make_peel},
        {{"clique", 3, "hint", true,
          "Find a large clique: more than K nodes means UNSAT without the solver; otherwise fix its nodes to colors 1..q (symmetry breaking).",
          "exact (Bron-Kerbosch instead of greedy), ms=N (time limit for exact, default 2000)"},
         make_clique},
    };
    return list;
}

}  // namespace

const std::vector<StrategyInfo>& strategy_list() {
    static const std::vector<StrategyInfo> list = [] {
        std::vector<StrategyInfo> out;
        for (const auto& e : entries()) out.push_back(e.info);
        return out;
    }();
    return list;
}

Plan run_strategies(const Graph& graph, const std::vector<std::string>& specs, const Context& context) {
    Plan plan;
    plan.graph = graph;
    plan.original_nodes = graph.num_nodes;
    plan.original.resize(graph.num_nodes + 1);
    for (int v = 0; v <= graph.num_nodes; v++) plan.original[v] = v;

    // name[:a,b=c] -> (entry, params), in pipeline order
    std::vector<std::pair<const Entry*, Params>> chosen;
    for (const auto& spec : specs) {
        std::string name = spec.substr(0, spec.find(':'));
        auto it = std::find_if(entries().begin(), entries().end(), [&](const Entry& e) { return e.info.name == name; });
        if (it == entries().end()) throw std::runtime_error("unknown strategy '" + name + "'");
        Params params;
        if (spec.find(':') != std::string::npos) {
            std::stringstream rest(spec.substr(spec.find(':') + 1));
            std::string item;
            while (std::getline(rest, item, ',')) {
                if (item.empty()) continue;
                size_t eq = item.find('=');
                params[item.substr(0, eq)] = eq == std::string::npos ? "" : item.substr(eq + 1);
            }
        }
        chosen.push_back({&*it, params});
    }
    std::stable_sort(chosen.begin(), chosen.end(), [](const auto& a, const auto& b) { return a.first->info.stage < b.first->info.stage; });
    if (chosen.empty()) return plan;

    // A self-loop makes the graph uncolorable; strategies that remove nodes must not hide it
    for (const auto& [u, v] : graph.edges) {
        if (u == v) {
            plan.decided = false;
            plan.reports.push_back({"self-loop", "node " + std::to_string(u) + " is its own neighbour, so no coloring exists", 0, {}, {}, {}, true});
            return plan;
        }
    }

    for (const auto& [entry, params] : chosen) {
        std::unique_ptr<Strategy> strategy = entry->make(params);
        Report report;
        report.name = entry->info.name;
        auto start = std::chrono::steady_clock::now();
        strategy->apply(plan, context, report);
        report.ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - start).count();
        plan.reports.push_back(report);
        if (plan.decided) break;
    }
    return plan;
}

}  // namespace strategies
