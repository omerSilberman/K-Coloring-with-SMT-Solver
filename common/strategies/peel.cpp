// peel (reduction): a node with fewer than K neighbours can always be colored last, with a
// color none of its neighbours has. So it is removed, and so on while such nodes remain
// (the K-core of the graph is what is left). The removed nodes are colored when the model
// is repaired, which needs the encoding's colors.
#include <queue>

#include "graph_tools.h"

namespace strategies {
namespace {

class Peel : public Strategy {
public:
    void apply(Plan& plan, const Context& context, Report& report) override {
        if (!context.colors) {
            report.text = "skipped: the encoding has no explicit colors to give the removed nodes";
            return;
        }
        int n = plan.graph.num_nodes;
        auto nb = neighbours_of(plan.graph);
        std::vector<int> degree(n + 1);
        std::vector<bool> removed(n + 1, false);
        std::queue<int> low;
        for (int v = 1; v <= n; v++) {
            degree[v] = (int)nb[v].size();
            if (degree[v] < context.K) low.push(v);
        }
        while (!low.empty()) {
            int u = low.front();
            low.pop();
            if (removed[u]) continue;
            removed[u] = true;
            Repair repair{Repair::Kind::FreeColor, plan.original[u], 0, {}};
            for (int w : nb[u]) {
                if (removed[w]) continue;
                repair.neighbours.push_back(plan.original[w]);
                if (--degree[w] < context.K) low.push(w);
            }
            plan.repairs.push_back(repair);
            report.removed.push_back(plan.original[u]);
        }
        int count = (int)report.removed.size();
        remove_nodes(plan, removed);
        report.text = "removed " + std::to_string(count) + " of " + std::to_string(n)
            + " nodes with fewer than K neighbours (colored afterwards); " + std::to_string(plan.graph.num_nodes)
            + " left";
    }
};

}  // namespace

std::unique_ptr<Strategy> make_peel(const Params& params) {
    if (!params.empty()) throw std::runtime_error("peel takes no parameters");
    return std::make_unique<Peel>();
}

}  // namespace strategies
