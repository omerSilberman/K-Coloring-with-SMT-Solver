// Set and relation encodings, all over any element theory: SET-CUBE, SET-MASK, SET-MEM, SET-CLASSES, REL-JOIN
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// ============================================================================
// THEORY OF FINITE SETS (Power Set Cube, any element theory)
// ============================================================================
// x is a subset of U = {e_0, ..., e_(L-1)} with 2^L >= K, so bit j of the color
// is "e_j in x". The 2^L - K subsets for the colors K..2^L-1 are forbidden one by
// one with x != S.
class SetCubeColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        int L = 0;
        while ((1 << L) < K) { L++; }

        ElementDomain domain = make_domain(L);
        cvc5::Sort set_sort = tm.mkSetSort(domain.sort);
        cvc5::Term universe = set_of(domain.elements, set_sort);
        vector<cvc5::Term> banned_sets;
        for (int b = K; b < (1 << L); b++) {
            banned_sets.push_back(set_of_bits(domain.elements, b, set_sort));
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(set_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], universe}));
            for (const auto& banned : banned_sets) {
                solver.assertFormula(tm.mkTerm(cvc5::Kind::DISTINCT, {node_vars[i], banned}));
            }
        }
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Subset masks - BV-AND with sets, any element theory)
// ============================================================================
// BV-AND with each bit-vector replaced by a set: bit j of x is "e_j in x", for L
// distinct elements e_0..e_(L-1) of any element theory, with 2^L >= K.
//   x subset U, U = {e_0, ..., e_(L-1)}          (the 2^L subsets of U)
//   not (x subset A_b) for each 1-bit b of E      (E = 2^L - K values excluded)
// A_b is the set of a_b = (E with bits b..0 cleared) | (2^b - 1), the same maximal
// element as in BV-AND: "x is not a subset of A_b" is (x & ~a_b) != 0. So the
// excluded subsets are the ones of {0, ..., E-1}, and K = 2^L needs no A_b at all.
class SetMaskColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        int L = 0;
        while ((1 << L) < K) { L++; }
        int excluded = (1 << L) - K;

        ElementDomain domain = make_domain(L);
        cvc5::Sort set_sort = tm.mkSetSort(domain.sort);
        cvc5::Term universe = set_of(domain.elements, set_sort);
        vector<cvc5::Term> forbidden;  // the A_b
        for (int b = 0; b < L; b++) {
            if (excluded >> b & 1) {
                int maximal = ((excluded >> (b + 1)) << (b + 1)) | ((1 << b) - 1);
                forbidden.push_back(set_of_bits(domain.elements, maximal, set_sort));
            }
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(set_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], universe}));
            for (const auto& a : forbidden) {
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT,
                    {tm.mkTerm(cvc5::Kind::SET_SUBSET, {node_vars[i], a})}));
            }
        }
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Element Membership Cube, any element theory)
// ============================================================================
// x in {e_1, ..., e_K}. SET-MEM-BV and SET-MEM-UF are SET-MEM-<ELEM> with BV and UF.
class SetMemberColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        cvc5::Term domain_set = set_of(domain.elements, tm.mkSetSort(domain.sort));
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_vars[i], domain_set}));
        }
    }
};

// ============================================================================
// THEORY OF FINITE SETS (Color classes instead of node colors, any element theory)
// ============================================================================
// The dual view: node i is the element id_i (n distinct elements), and there are
// K set variables S_1..S_K of node ids, one per color class.
//   partition:   S_1 u ... u S_K = {id_1, ..., id_n} and S_a n S_b = {} for a != b
//   independent: for every edge (u, v) and color c, not (id_u in S_c and id_v in S_c)
// There are no node variables at all; a node's color is the class it is in.
class SetClassesColorer : public ElementGenericColorer {
private:
    vector<cvc5::Term> node_ids;
    vector<cvc5::Term> classes;
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    string container_logic() const override { return "FS"; }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(num_nodes);
        node_ids = domain.elements;
        cvc5::Sort set_sort = tm.mkSetSort(domain.sort);
        cvc5::Term empty_set = tm.mkEmptySet(set_sort);
        cvc5::Term all_nodes = set_of(node_ids, set_sort);

        for (int c = 1; c <= K; c++) {
            classes.push_back(tm.mkConst(set_sort, "S_" + to_string(c)));
        }
        cvc5::Term all_classes = classes[0];
        for (int c = 1; c < K; c++) {
            all_classes = tm.mkTerm(cvc5::Kind::SET_UNION, {all_classes, classes[c]});
        }
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {all_classes, all_nodes}));
        for (int a = 0; a < K; a++) {
            for (int b = a + 1; b < K; b++) {
                cvc5::Term overlap = tm.mkTerm(cvc5::Kind::SET_INTER, {classes[a], classes[b]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {overlap, empty_set}));
            }
        }
    }
    cvc5::Term member(int node, int c) {
        return tm.mkTerm(cvc5::Kind::SET_MEMBER, {node_ids[node - 1], classes[c]});
    }
    cvc5::Term edge_constraint_between(int u, int v) override {
        vector<cvc5::Term> apart;
        for (int c = 0; c < K; c++) {
            apart.push_back(tm.mkTerm(cvc5::Kind::NOT,
                {tm.mkTerm(cvc5::Kind::AND, {member(u, c), member(v, c)})}));
        }
        return (K == 1) ? apart[0] : tm.mkTerm(cvc5::Kind::AND, apart);
    }
    void print_model() override {
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int c = 0; c < K && color == 0; c++) {
                if (solver.getValue(member(i, c)).getBooleanValue()) color = c + 1;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

// ============================================================================
// THEORY OF RELATIONS (The whole graph as one relational constraint, any element theory)
// ============================================================================
// Relations are sets of tuples. Nodes and colors are both named by elements: node i
// is id_i and color c is id_c, from max(n, K) distinct elements. E = {(u, v) | edge}
// is a constant, and the coloring is an unknown relation C between nodes and colors:
//   C subset Nodes x Colors       (Nodes = {(id_1), ..., (id_n)}, Colors = {(id_1), ..., (id_K)})
//   C join Colors = Nodes         (every node has at least one color)
//   (E join C) n C = {}           (the coloring constraint)
// E join C = {(u, c) | edge (u, v) and (v, c) in C}: the colors of u's neighbours.
// The last line says no node shares a color with a neighbour, for all edges at once.
// C does not have to be a function: if a node gets several colors, any one of them
// still gives a valid coloring, so a "functional" constraint would only add work.
class RelJoinColorer : public ElementGenericColorer {
private:
    vector<cvc5::Term> ids;
    cvc5::Term coloring;
    cvc5::Term pair(int a, int b) { return tm.mkTuple({ids[a - 1], ids[b - 1]}); }
    cvc5::Term relation(const vector<cvc5::Term>& tuples, const cvc5::Sort& sort) {
        return set_of(tuples, sort);
    }
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    // Tuples (relations) on top of sets have no SMT-LIB logic name
    void configure_theory() override { solver.setLogic("ALL"); }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(max(num_nodes, K));
        ids = domain.elements;
        cvc5::Sort unary_sort = tm.mkSetSort(tm.mkTupleSort({domain.sort}));
        cvc5::Sort binary_sort = tm.mkSetSort(tm.mkTupleSort({domain.sort, domain.sort}));

        vector<cvc5::Term> node_tuples, color_tuples, edge_tuples;
        for (int i = 1; i <= num_nodes; i++) node_tuples.push_back(tm.mkTuple({ids[i - 1]}));
        for (int c = 1; c <= K; c++) color_tuples.push_back(tm.mkTuple({ids[c - 1]}));
        for (const auto& edge : edges) edge_tuples.push_back(pair(edge.first, edge.second));
        cvc5::Term nodes_rel = relation(node_tuples, unary_sort);
        cvc5::Term colors_rel = relation(color_tuples, unary_sort);
        cvc5::Term edges_rel = relation(edge_tuples, binary_sort);

        coloring = tm.mkConst(binary_sort, "C");
        cvc5::Term domain_rel = tm.mkTerm(cvc5::Kind::RELATION_PRODUCT, {nodes_rel, colors_rel});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::SET_SUBSET, {coloring, domain_rel}));
        cvc5::Term colored = tm.mkTerm(cvc5::Kind::RELATION_JOIN, {coloring, colors_rel});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {colored, nodes_rel}));
        cvc5::Term neighbour_colors = tm.mkTerm(cvc5::Kind::RELATION_JOIN, {edges_rel, coloring});
        cvc5::Term clashes = tm.mkTerm(cvc5::Kind::SET_INTER, {neighbour_colors, coloring});
        solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {clashes, tm.mkEmptySet(binary_sort)}));
    }
    // All edges are in the single constraint above
    cvc5::Term edge_constraint_between(int, int) override { return cvc5::Term(); }
    void print_model() override {
        // A node's color is its smallest color in C
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int c = 1; c <= K && color == 0; c++) {
                cvc5::Term has_c = tm.mkTerm(cvc5::Kind::SET_MEMBER, {pair(i, c), coloring});
                if (solver.getValue(has_c).getBooleanValue()) color = c;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

}  // namespace

void register_sets(Cvc5Registry& registry) {
    registry.add_generic("SET-CUBE", "INT", make_generic<SetCubeColorer>());
    registry.add_generic("SET-MASK", "INT", make_generic<SetMaskColorer>());
    registry.add_generic("SET-MEM", "INT", make_generic<SetMemberColorer>());
    registry.add_generic("SET-CLASSES", "INT", make_generic<SetClassesColorer>());
    registry.add_generic("REL-JOIN", "INT", make_generic<RelJoinColorer>());
}
