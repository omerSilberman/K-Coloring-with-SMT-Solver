// clique (hint): a clique needs as many colors as it has nodes.
//   - a clique of more than K nodes: no K-coloring, answered without the solver
//   - otherwise its nodes get the colors 1..q, fixed in the formula. Any coloring can have
//     its colors renamed so that the clique gets exactly these, so this keeps the answer
//     and removes the K! renamings of every coloring from the search (symmetry breaking).
// Search: greedy from the 64 highest-degree nodes (default), or exact (Bron-Kerbosch with
// pivoting) within ms milliseconds, keeping the best clique found.
#include <algorithm>

#include "graph_tools.h"

namespace strategies {
namespace {

class Clique : public Strategy {
    bool exact;
    int ms;
    std::vector<int> best;
    bool complete = true;  // the exact search finished
    std::unique_ptr<Deadline> deadline;

    // Greedy: start at s, keep adding the candidate adjacent to the most other candidates
    std::vector<int> greedy_from(const BitGraph& g, int s) {
        std::vector<int> clique{s};
        std::vector<uint64_t> candidates = g.rows[s];
        while (BitGraph::count(candidates)) {
            int pick = 0, pick_score = -1;
            for (int v = 1; v <= g.n; v++) {
                if (!BitGraph::test(candidates, v)) continue;
                int score = 0;
                for (int i = 0; i < g.words; i++) score += __builtin_popcountll(g.rows[v][i] & candidates[i]);
                if (score > pick_score) { pick = v; pick_score = score; }
            }
            clique.push_back(pick);
            for (int i = 0; i < g.words; i++) candidates[i] &= g.rows[pick][i];
        }
        return clique;
    }

    // Bron-Kerbosch with pivoting: R the clique so far, P the candidates, X the excluded
    void expand(const BitGraph& g, std::vector<int>& R, std::vector<uint64_t> P, std::vector<uint64_t> X) {
        if (deadline->passed()) { complete = false; return; }
        if ((int)R.size() + BitGraph::count(P) <= (int)best.size()) return;  // cannot beat best
        if (!BitGraph::count(P)) {
            if (!BitGraph::count(X) && R.size() > best.size()) best = R;
            return;
        }
        // pivot: the node of P u X with the most neighbours in P
        int pivot = 0, pivot_score = -1;
        for (int v = 1; v <= g.n; v++) {
            if (!BitGraph::test(P, v) && !BitGraph::test(X, v)) continue;
            int score = 0;
            for (int i = 0; i < g.words; i++) score += __builtin_popcountll(g.rows[v][i] & P[i]);
            if (score > pivot_score) { pivot = v; pivot_score = score; }
        }
        for (int v = 1; v <= g.n; v++) {
            if (!BitGraph::test(P, v) || BitGraph::test(g.rows[pivot], v)) continue;
            std::vector<uint64_t> P2(g.words), X2(g.words);
            for (int i = 0; i < g.words; i++) {
                P2[i] = P[i] & g.rows[v][i];
                X2[i] = X[i] & g.rows[v][i];
            }
            R.push_back(v);
            expand(g, R, P2, X2);
            R.pop_back();
            if (!complete) return;
            BitGraph::clear(P, v);
            BitGraph::set(X, v);
        }
    }

public:
    Clique(bool exact, int ms) : exact(exact), ms(ms) {}

    void apply(Plan& plan, const Context& context, Report& report) override {
        int n = plan.graph.num_nodes;
        if (n == 0) {
            report.text = "the graph is empty";
            return;
        }
        BitGraph g(neighbours_of(plan.graph));
        std::vector<int> order;
        for (int v = 1; v <= n; v++) order.push_back(v);
        std::sort(order.begin(), order.end(), [&](int a, int b) {
            return BitGraph::count(g.rows[a]) > BitGraph::count(g.rows[b]);
        });
        for (int i = 0; i < std::min(n, 64); i++) {
            std::vector<int> clique = greedy_from(g, order[i]);
            if (clique.size() > best.size()) best = clique;
        }
        std::string how = "greedy";
        if (exact) {
            deadline = std::make_unique<Deadline>(ms);
            std::vector<int> R;
            std::vector<uint64_t> P(g.words, 0), X(g.words, 0);
            for (int v = 1; v <= n; v++) BitGraph::set(P, v);
            expand(g, R, P, X);
            how = complete ? "exact, the largest" : "best found in " + std::to_string(ms) + " ms";
        }
        std::sort(best.begin(), best.end());
        int q = (int)best.size();
        for (int v : best) report.clique.push_back(plan.original[v]);
        std::string nodes;
        for (int v : report.clique) nodes += (nodes.empty() ? "" : " ") + std::to_string(v);
        std::string found = "clique of " + std::to_string(q) + " (" + how + "; nodes " + nodes + ")";

        if (q > context.K) {
            plan.decided = false;
            report.decided = true;
            report.text = found + ": more than K = " + std::to_string(context.K)
                + " nodes that all need different colors, so no K-coloring exists (no solver needed)";
        } else if (!context.colors) {
            report.text = found + "; colors not fixed: the encoding has no explicit colors";
        } else {
            for (int i = 0; i < q; i++) {
                plan.fixed.push_back({best[i], i});
                report.fixed.push_back({plan.original[best[i]], i});
            }
            report.text = found + ", fixed to colors 1.." + std::to_string(q);
        }
    }
};

}  // namespace

std::unique_ptr<Strategy> make_clique(const Params& params) {
    for (const auto& [name, value] : params) {
        if (name != "exact" && name != "ms") throw std::runtime_error("clique: unknown parameter '" + name + "' (exact, ms=N)");
    }
    return std::make_unique<Clique>(params.count("exact") > 0, int_param(params, "ms", 2000));
}

}  // namespace strategies
