// dominated (reduction): if u and v are not adjacent and every neighbour of u is also a
// neighbour of v, then in any coloring u can take v's color. So u is removed, and gets v's
// color back when the model is repaired. Repeats until no node is dominated (or ms runs out).
#include <algorithm>

#include "graph_tools.h"

namespace strategies {
namespace {

class Dominated : public Strategy {
    int ms;
public:
    explicit Dominated(int ms) : ms(ms) {}
    void apply(Plan& plan, const Context&, Report& report) override {
        int n = plan.graph.num_nodes;
        auto nb = neighbours_of(plan.graph);
        BitGraph bits(nb);
        std::vector<bool> removed(n + 1, false);
        Deadline deadline(ms);
        bool timed_out = false;

        // u's neighbours are a subset of v's (both not removed, u != v, not adjacent)
        auto dominated_by = [&](int u, int v) {
            if (v == u || removed[v] || bits.adjacent(u, v)) return false;
            for (int i = 0; i < bits.words; i++) {
                if (bits.rows[u][i] & ~bits.rows[v][i]) return false;
            }
            return true;
        };

        bool changed = true;
        while (changed && !timed_out) {
            changed = false;
            std::vector<int> order;
            for (int v = 1; v <= n; v++) if (!removed[v]) order.push_back(v);
            std::sort(order.begin(), order.end(), [&](int a, int b) {
                return BitGraph::count(bits.rows[a]) < BitGraph::count(bits.rows[b]);
            });
            for (int u : order) {
                if (deadline.passed()) { timed_out = true; break; }
                if (removed[u]) continue;
                // candidates: the neighbours of one neighbour of u (any node if u is isolated)
                int dominator = 0, pivot = 0;
                for (int w : nb[u]) if (!removed[w]) { pivot = w; break; }
                if (pivot) {
                    for (int v : nb[pivot]) if (dominated_by(u, v)) { dominator = v; break; }
                } else {
                    for (int v = 1; v <= n && !dominator; v++) if (dominated_by(u, v)) dominator = v;
                }
                if (!dominator) continue;
                removed[u] = true;
                for (int w : nb[u]) BitGraph::clear(bits.rows[w], u);
                std::fill(bits.rows[u].begin(), bits.rows[u].end(), 0);
                plan.repairs.push_back({Repair::Kind::CopyColor, plan.original[u], plan.original[dominator], {}});
                report.removed.push_back(plan.original[u]);
                changed = true;
            }
        }
        int count = (int)report.removed.size();
        remove_nodes(plan, removed);
        report.text = "removed " + std::to_string(count) + " of " + std::to_string(n)
            + " nodes whose neighbours are all neighbours of another, non-adjacent node (each copies that node's color)"
            + (timed_out ? "; stopped after " + std::to_string(ms) + " ms" : "");
    }
};

}  // namespace

std::unique_ptr<Strategy> make_dominated(const Params& params) {
    for (const auto& [name, value] : params) {
        if (name != "ms") throw std::runtime_error("dominated: unknown parameter '" + name + "' (ms=N)");
    }
    return std::make_unique<Dominated>(int_param(params, "ms", 2000));
}

}  // namespace strategies
