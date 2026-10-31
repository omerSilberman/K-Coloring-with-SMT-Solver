// Bag (multiset) encodings, all over any element theory: BAG-SUB, BAG-UNARY, BAG-CARD,
// BAG-NEIGHBORS (see the README, "Bags"). cvc5 has no logic name for bags (FB), so they
// run in ALL.
#include "colorer.h"
#include "elements.h"
#include "../common/util.h"
#include "registry.h"

namespace {

// Base: logic ALL, and the bag operations the encodings share
class BagColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    void configure_theory() override { solver.setLogic("ALL"); }
    // The bag with e repeated n times
    cvc5::Term bag_of(const cvc5::Term& e, int n) {
        return tm.mkTerm(cvc5::Kind::BAG_MAKE, {e, tm.mkInteger(n)});
    }
    // b_1 + ... + b_n (counts add up); the empty bag of bag_sort for no bags
    cvc5::Term disjoint_union(const vector<cvc5::Term>& bags, const cvc5::Sort& bag_sort) {
        if (bags.empty()) return tm.mkEmptyBag(bag_sort);
        cvc5::Term all = bags[0];
        for (size_t i = 1; i < bags.size(); i++) all = tm.mkTerm(cvc5::Kind::BAG_UNION_DISJOINT, {all, bags[i]});
        return all;
    }
};

// A node is a sub-bag of B = {e_1:m_1, ..., e_L:m_L}. B has (m_1+1)...(m_L+1) sub-bags (each
// e_i appears 0..m_i times), so choosing the m_i with that product equal to K makes the
// domain exactly K values with a single constraint, x subbag B, and nothing to exclude.
// It is a mixed-radix number: e_i's count is a digit in base m_i + 1.
//   BAG-SUB:    one element per prime factor p of K, with multiplicity p - 1
//               (K = 12 = 2*2*3: {e_1:1, e_2:1, e_3:2}); as close to bits as K allows
//   BAG-UNARY:  one element with multiplicity K - 1 ({e_1:11} for K = 12): a count 0..K-1
// For K = 2^L, BAG-SUB is {e_1:1, ..., e_L:1}: the bag version of SET-CUBE.
class BagSubColorer : public BagColorer {
private:
    bool unary;
public:
    BagSubColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements, bool unary)
        : BagColorer(k, model, print, std::move(elements)), unary(unary) {}
protected:
    void build_variables_and_bounds() override {
        vector<int> multiplicities;
        if (unary) {
            if (K > 1) multiplicities.push_back(K - 1);
        } else {
            for (int p : prime_factors(K)) multiplicities.push_back(p - 1);
        }
        ElementDomain domain = make_domain(multiplicities.size());
        cvc5::Sort bag_sort = tm.mkBagSort(domain.sort);
        vector<cvc5::Term> parts;
        for (size_t i = 0; i < multiplicities.size(); i++) parts.push_back(bag_of(domain.elements[i], multiplicities[i]));
        cvc5::Term B = disjoint_union(parts, bag_sort);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(bag_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::BAG_SUBBAG, {node_vars[i], B}));
        }
    }
};

// No domain constraint per node: the nodes are free values of the element sort, edges are
// u != v, and one constraint says at most K distinct values occur:
//   |setof({x_1:1} + ... + {x_n:1})| <= K
// (setof keeps one copy of each element). The bag-theory counterpart of UF-CARD: the
// same "at most K colors" stated as arithmetic over a term instead of a property of the sort.
// The element theory only provides the sort, which must hold at least K values.
class BagCardColorer : public BagColorer {
public:
    using BagColorer::BagColorer;
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = element_theory->make_domain(tm, K);  // the sort; the elements are not used
        cvc5::Sort bag_sort = tm.mkBagSort(domain.sort);
        vector<cvc5::Term> singletons;
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            singletons.push_back(bag_of(node_vars[i], 1));
        }
        cvc5::Term distinct = tm.mkTerm(cvc5::Kind::BAG_SETOF, {disjoint_union(singletons, bag_sort)});
        cvc5::Term count = tm.mkTerm(cvc5::Kind::BAG_CARD, {distinct});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {count, tm.mkInteger(K)}));
    }
};

// Neighbours differ, stated once per node instead of once per edge: the colors of v's
// neighbours form a bag N_v, and v's own color occurs in it zero times:
//   x_v in {e_1, ..., e_K}        N_v = sum over neighbours u of {x_u:1}       count(x_v, N_v) = 0
// (Replacing = 0 by <= d would give defective coloring: at most d same-colored neighbours.)
class BagNeighborsColorer : public BagColorer {
public:
    using BagColorer::BagColorer;
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        cvc5::Sort bag_sort = tm.mkBagSort(domain.sort);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            vector<cvc5::Term> choices;
            for (const auto& e : domain.elements) choices.push_back(tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], e}));
            solver.assertFormula(K == 1 ? choices[0] : tm.mkTerm(cvc5::Kind::OR, choices));
        }
        vector<vector<int>> neighbours(num_nodes + 1);
        for (const auto& [u, v] : edges) {
            neighbours[u].push_back(v);
            if (u != v) neighbours[v].push_back(u);
        }
        for (int v = 1; v <= num_nodes; v++) {
            if (neighbours[v].empty()) continue;
            vector<cvc5::Term> colors;
            for (int u : neighbours[v]) colors.push_back(bag_of(node_vars[u], 1));
            cvc5::Term count = tm.mkTerm(cvc5::Kind::BAG_COUNT, {node_vars[v], disjoint_union(colors, bag_sort)});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {count, tm.mkInteger(0)}));
        }
    }
    // All edges are in the per-node constraints above
    cvc5::Term edge_constraint_between(int, int) override { return cvc5::Term(); }
};

}  // namespace

void register_bags(Cvc5Registry& registry) {
    registry.add_generic("BAG-SUB", "INT", make_generic<BagSubColorer>(false));
    registry.add_generic("BAG-UNARY", "INT", make_generic<BagSubColorer>(true));
    registry.add_generic("BAG-CARD", "UF", make_generic<BagCardColorer>());
    registry.add_generic("BAG-NEIGHBORS", "INT", make_generic<BagNeighborsColorer>());
}
