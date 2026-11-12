// Graph helpers shared by the strategies (internal to common/strategies/).
#pragma once

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "strategy.h"

namespace strategies {

// Neighbour lists of g, without duplicate edges or self-loops (index 0 unused)
inline std::vector<std::vector<int>> neighbours_of(const Graph& g) {
    std::vector<std::vector<int>> nb(g.num_nodes + 1);
    for (const auto& [u, v] : g.edges) {
        if (u == v || u < 1 || v < 1 || u > g.num_nodes || v > g.num_nodes) continue;
        nb[u].push_back(v);
        nb[v].push_back(u);
    }
    for (auto& list : nb) {
        std::sort(list.begin(), list.end());
        list.erase(std::unique(list.begin(), list.end()), list.end());
    }
    return nb;
}

// Adjacency as bitsets, for subset tests and clique search
struct BitGraph {
    int n = 0, words = 0;
    std::vector<std::vector<uint64_t>> rows;  // rows[v]: the neighbours of v

    explicit BitGraph(const std::vector<std::vector<int>>& nb) : n((int)nb.size() - 1), words(((int)nb.size() + 63) / 64) {
        rows.assign(n + 1, std::vector<uint64_t>(words, 0));
        for (int u = 1; u <= n; u++) {
            for (int v : nb[u]) set(rows[u], v);
        }
    }
    static void set(std::vector<uint64_t>& bits, int i) { bits[i >> 6] |= uint64_t(1) << (i & 63); }
    static void clear(std::vector<uint64_t>& bits, int i) { bits[i >> 6] &= ~(uint64_t(1) << (i & 63)); }
    static bool test(const std::vector<uint64_t>& bits, int i) { return bits[i >> 6] >> (i & 63) & 1; }
    static int count(const std::vector<uint64_t>& bits) {
        int c = 0;
        for (uint64_t w : bits) c += __builtin_popcountll(w);
        return c;
    }
    bool adjacent(int u, int v) const { return test(rows[u], v); }
};

// Takes the nodes with removed[v] = true out of the plan: renumbers the graph, original
// and fixed (current ids)
inline void remove_nodes(Plan& plan, const std::vector<bool>& removed) {
    std::vector<int> new_id(plan.graph.num_nodes + 1, 0);
    std::vector<int> original{0};
    for (int v = 1; v <= plan.graph.num_nodes; v++) {
        if (removed[v]) continue;
        new_id[v] = (int)original.size();
        original.push_back(plan.original[v]);
    }
    Graph g;
    g.num_nodes = (int)original.size() - 1;
    for (const auto& [u, v] : plan.graph.edges) {
        if (new_id[u] && new_id[v]) g.edges.push_back({new_id[u], new_id[v]});
    }
    g.num_edges = (int)g.edges.size();
    std::vector<std::pair<int, int>> fixed;
    for (const auto& [v, c] : plan.fixed) {
        if (new_id[v]) fixed.push_back({new_id[v], c});
    }
    plan.graph = g;
    plan.original = original;
    plan.fixed = fixed;
}

// Strategy parameters: "exact,ms=500" -> {exact: "", ms: "500"}
using Params = std::map<std::string, std::string>;

inline int int_param(const Params& params, const std::string& name, int fallback) {
    auto it = params.find(name);
    if (it == params.end()) return fallback;
    try {
        return std::stoi(it->second);
    } catch (...) {
        throw std::runtime_error("strategy parameter " + name + " needs a number, got '" + it->second + "'");
    }
}

// A time budget in milliseconds
struct Deadline {
    std::chrono::steady_clock::time_point end;
    explicit Deadline(int ms) : end(std::chrono::steady_clock::now() + std::chrono::milliseconds(ms)) {}
    bool passed() const { return std::chrono::steady_clock::now() > end; }
};

// The factories, one per strategy file
std::unique_ptr<Strategy> make_dsatur(const Params& params);
std::unique_ptr<Strategy> make_dominated(const Params& params);
std::unique_ptr<Strategy> make_peel(const Params& params);
std::unique_ptr<Strategy> make_clique(const Params& params);

}  // namespace strategies
