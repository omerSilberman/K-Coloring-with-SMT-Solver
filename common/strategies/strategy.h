// Strategies: graph reasoning done before the solver runs, the same for every engine and
// encoding. A strategy never builds a term. It changes a Plan: the graph to encode, the
// colors some nodes must get, or an answer found without the solver, plus how to turn a
// model of the reduced graph back into a coloring of the original one.
//
// Three kinds, run in this order (the stage):
//   pre-checks   answer without the solver (dsatur)
//   reductions   remove nodes, and repair their colors afterwards (dominated, peel)
//   hints        add constraints to the formula (clique: fix the colors of a clique)
// Fixing a node's color is the only thing that needs the encoding: GraphColorer::fix_color,
// which encodings with explicit color terms support (supports_colors()).
#pragma once

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "../graph.h"

namespace strategies {

// Undoes one node removal (repairs are undone in reverse order). Node ids are original ids.
struct Repair {
    enum class Kind { CopyColor, FreeColor };
    Kind kind;
    int node;
    int source = 0;                // CopyColor: give node the color of source
    std::vector<int> neighbours;   // FreeColor: give node a color none of these has
};

// What one strategy did, for the output (original node ids)
struct Report {
    std::string name;
    std::string text;
    double ms = 0;
    std::vector<int> removed;                      // nodes taken out of the formula
    std::vector<std::pair<int, int>> fixed;        // node -> color (0-based) fixed in the formula
    std::vector<int> clique;
    bool decided = false;                          // the strategy answered without the solver
};

struct Plan {
    Graph graph;                                   // what to encode, nodes renumbered 1..n
    std::vector<int> original;                     // current id -> original id (index 0 unused)
    int original_nodes = 0;
    std::vector<std::pair<int, int>> fixed;        // current id -> color 0..K-1
    std::optional<bool> decided;                   // true = SAT, false = UNSAT, found without the solver
    std::vector<int> decided_colors;               // SAT: original id -> color 0..K-1
    std::vector<Repair> repairs;
    std::vector<Report> reports;
};

struct Context {
    int K;
    bool colors;   // the encoding can fix a node's color (supports_colors())
};

class Strategy {
public:
    virtual ~Strategy() = default;
    virtual void apply(Plan& plan, const Context& context, Report& report) = 0;
};

// One registered strategy
struct StrategyInfo {
    std::string name;
    int stage;                 // 0 pre-check, 1-2 reductions, 3 hints
    std::string kind;          // "pre-check", "reduction", "hint"
    bool needs_colors;         // does nothing useful without explicit colors (see description)
    std::string description;
    std::string parameters;    // accepted NAME:PARAMS, "" if none
};

// Every strategy, in pipeline order
const std::vector<StrategyInfo>& strategy_list();

// Runs the strategies named in specs ("clique", "clique:exact", ...) in pipeline order,
// whatever order specs has. Throws on an unknown name or parameter.
Plan run_strategies(const Graph& graph, const std::vector<std::string>& specs, const Context& context);

}  // namespace strategies
