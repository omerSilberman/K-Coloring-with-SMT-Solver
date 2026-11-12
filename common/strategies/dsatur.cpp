// dsatur (pre-check): Brelaz's DSATUR heuristic. If it colors the graph with at most K
// colors, the answer is SAT and the solver is not needed. It cannot prove UNSAT.
#include <algorithm>
#include <set>

#include "graph_tools.h"

namespace strategies {
namespace {

class Dsatur : public Strategy {
public:
    void apply(Plan& plan, const Context& context, Report& report) override {
        int n = plan.graph.num_nodes;
        auto nb = neighbours_of(plan.graph);
        std::vector<int> color(n + 1, -1);
        std::vector<std::set<int>> seen(n + 1);  // the distinct colors among each node's neighbours
        int used = 0;
        for (int step = 0; step < n; step++) {
            // the uncolored node with the most distinct neighbour colors, then the most neighbours
            int best = 0;
            for (int v = 1; v <= n; v++) {
                if (color[v] >= 0) continue;
                if (!best || seen[v].size() > seen[best].size()
                    || (seen[v].size() == seen[best].size() && nb[v].size() > nb[best].size())) best = v;
            }
            int c = 0;
            while (seen[best].count(c)) c++;
            color[best] = c;
            used = std::max(used, c + 1);
            for (int w : nb[best]) seen[w].insert(c);
        }
        if (used <= context.K) {
            plan.decided = true;
            plan.decided_colors.assign(plan.original_nodes + 1, 0);
            for (int v = 1; v <= n; v++) plan.decided_colors[plan.original[v]] = color[v];
            report.decided = true;
            report.text = "colored the graph with " + std::to_string(used) + " colors (K = " + std::to_string(context.K)
                + "), so it is K-colorable without the solver";
        } else {
            report.text = "needs " + std::to_string(used) + " colors, more than K = " + std::to_string(context.K)
                + ": not decided, the solver runs";
        }
    }
};

}  // namespace

std::unique_ptr<Strategy> make_dsatur(const Params& params) {
    if (!params.empty()) throw std::runtime_error("dsatur takes no parameters");
    return std::make_unique<Dsatur>();
}

}  // namespace strategies
