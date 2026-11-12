// Set and relation encodings, all over any element theory: SET-CUBE, SET-MASK, SET-MEM,
// SET-CLASSES, REL-JOIN (see cvc5/sets.cpp and the README). Z3's sets are arrays from
// the element sort to Bool.
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// x subset {e_0, ..., e_(L-1)} with 2^L >= K; the 2^L - K extra subsets are forbidden
// one by one with x != S
class SetCubeColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void build_variables_and_bounds() override {
        int L = 0;
        while ((1 << L) < K) { L++; }
        ElementDomain domain = make_domain(L);
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(set_of_bits(domain.elements, c, domain.sort));
        }
        z3::expr universe = set_of(domain.elements, domain.sort);
        vector<z3::expr> banned_sets;
        for (int b = K; b < (1 << L); b++) banned_sets.push_back(set_of_bits(domain.elements, b, domain.sort));

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), set_sort(domain.sort));
            solver.add(z3::set_subset(node_vars[i], universe));
            for (const auto& banned : banned_sets) solver.add(node_vars[i] != banned);
        }
    }
};

// BV-AND with sets: x subset U, and not (x subset A_b) for each 1-bit b of 2^L - K
class SetMaskColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void build_variables_and_bounds() override {
        int L = 0;
        while ((1 << L) < K) { L++; }
        int excluded = (1 << L) - K;
        ElementDomain domain = make_domain(L);
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(set_of_bits(domain.elements, excluded + c, domain.sort));  // E..2^L-1
        }
        z3::expr universe = set_of(domain.elements, domain.sort);
        vector<z3::expr> forbidden;  // the A_b
        for (int b = 0; b < L; b++) {
            if (excluded >> b & 1) {
                int maximal = ((excluded >> (b + 1)) << (b + 1)) | ((1 << b) - 1);
                forbidden.push_back(set_of_bits(domain.elements, maximal, domain.sort));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), set_sort(domain.sort));
            solver.add(z3::set_subset(node_vars[i], universe));
            for (const auto& a : forbidden) solver.add(!z3::set_subset(node_vars[i], a));
        }
    }
};

// x in {e_1, ..., e_K}
class SetMemberColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        colors = domain.elements;
        z3::expr domain_set = set_of(domain.elements, domain.sort);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), domain.sort);
            solver.add(member(node_vars[i], domain_set));
        }
    }
};

// No node variables: K sets S_1..S_K of node ids that partition all nodes, and no edge
// has both ends in the same S_c
class SetClassesColorer : public ElementGenericColorer {
private:
    vector<z3::expr> node_ids;
    vector<z3::expr> classes;
public:
    using ElementGenericColorer::ElementGenericColorer;
public:
    bool supports_colors() const override { return true; }
    // color j is the class S_j; the model prints colors as 1..K
    void fix_color(int node, int color) override { solver.add(in_class(node, color)); }
    string color_value(int color) override { return to_string(color + 1); }
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(num_nodes);
        node_ids = domain.elements;
        z3::expr empty = z3::empty_set(domain.sort);
        z3::expr all_nodes = set_of(node_ids, domain.sort);

        for (int c = 1; c <= K; c++) classes.push_back(constant("S_" + to_string(c), set_sort(domain.sort)));
        z3::expr all_classes = classes[0];
        for (int c = 1; c < K; c++) all_classes = z3::set_union(all_classes, classes[c]);
        solver.add(all_classes == all_nodes);
        for (int a = 0; a < K; a++) {
            for (int b = a + 1; b < K; b++) solver.add(z3::set_intersect(classes[a], classes[b]) == empty);
        }
    }
    z3::expr in_class(int node, int c) { return member(node_ids[node - 1], classes[c]); }
    optional<z3::expr> edge_constraint_between(int u, int v) override {
        vector<z3::expr> apart;
        for (int c = 0; c < K; c++) apart.push_back(!(in_class(u, c) && in_class(v, c)));
        return all_of(apart);
    }
    void print_model() override {
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int c = 0; c < K && color == 0; c++) {
                if (value(in_class(i, c)).is_true()) color = c + 1;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

// The whole graph as one relational constraint. Z3 has no relations (rel.join,
// rel.product), so relations are sets of tuple datatypes, and the two relational
// operators are written out as lambdas. The joined column ranges over a finite set
// (the colors, or the nodes), so the join is a finite disjunction rather than an
// existential:
//   Nodes x Colors   = lambda (n, c). (n) in Nodes and (c) in Colors
//   C join Colors    = lambda (n). OR over colors c of ((n, c) in C and (c) in Colors)
//   E join C         = lambda (u, c). OR over nodes v of ((u, v) in E and (v, c) in C)
// and the constraints are those of cvc5's REL-JOIN:
//   C subset Nodes x Colors,  C join Colors = Nodes,  (E join C) n C = {}
// (With "exists v" inside the lambda instead, Z3 5.1 answered SAT with an invalid model
// on K_4 with BV elements: model-based quantifier instantiation accepted a model it
// could not check. The quantifier-free version has no such problem.)
class RelJoinColorer : public ElementGenericColorer {
private:
    vector<z3::expr> ids;
    optional<z3::expr> coloring;
    optional<z3::func_decl> mk_pair;
    z3::expr pair(int a, int b) { return (*mk_pair)(ids[a - 1], ids[b - 1]); }
public:
    using ElementGenericColorer::ElementGenericColorer;
public:
    bool supports_colors() const override { return true; }
    // color j is the pair (node, j) in C; the model prints colors as 1..K
    void fix_color(int node, int color) override { solver.add(member(pair(node, color + 1), *coloring)); }
    string color_value(int color) override { return to_string(color + 1); }
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(max(num_nodes, K));
        ids = domain.elements;
        const char* unary_names[] = {"value"};
        const char* pair_names[] = {"first", "second"};
        z3::sort unary_fields[] = {domain.sort};
        z3::sort pair_fields[] = {domain.sort, domain.sort};
        z3::func_decl_vector unary_proj(ctx), pair_proj(ctx);
        z3::func_decl mk_unary = ctx.tuple_sort("Unary", 1, unary_names, unary_fields, unary_proj);
        mk_pair = ctx.tuple_sort("Pair", 2, pair_names, pair_fields, pair_proj);
        z3::sort unary_sort = mk_unary.range(), pair_sort = mk_pair->range();

        vector<z3::expr> node_tuples, color_tuples, edge_tuples;
        for (int i = 1; i <= num_nodes; i++) node_tuples.push_back(mk_unary(ids[i - 1]));
        for (int c = 1; c <= K; c++) color_tuples.push_back(mk_unary(ids[c - 1]));
        for (const auto& edge : edges) edge_tuples.push_back(pair(edge.first, edge.second));
        z3::expr nodes_rel = set_of(node_tuples, unary_sort);
        z3::expr colors_rel = set_of(color_tuples, unary_sort);
        z3::expr edges_rel = set_of(edge_tuples, pair_sort);

        coloring = constant("C", set_sort(pair_sort));
        z3::expr C = *coloring;
        z3::expr p = constant("p", pair_sort), q = constant("q", unary_sort);
        z3::expr first = pair_proj[0](p), second = pair_proj[1](p);

        z3::expr product = z3::lambda(p, member(mk_unary(first), nodes_rel) && member(mk_unary(second), colors_rel));
        solver.add(z3::set_subset(C, product));
        vector<z3::expr> has_color;  // OR over colors c
        for (int c = 1; c <= K; c++) {
            has_color.push_back(member((*mk_pair)(unary_proj[0](q), ids[c - 1]), C) && member(mk_unary(ids[c - 1]), colors_rel));
        }
        solver.add(z3::lambda(q, any_of(has_color)) == nodes_rel);
        vector<z3::expr> via_neighbour;  // OR over nodes v
        for (int v = 1; v <= num_nodes; v++) {
            via_neighbour.push_back(member((*mk_pair)(first, ids[v - 1]), edges_rel) && member((*mk_pair)(ids[v - 1], second), C));
        }
        z3::expr neighbour_colors = z3::lambda(p, any_of(via_neighbour));
        solver.add(z3::set_intersect(neighbour_colors, C) == z3::empty_set(pair_sort));
    }
    // All edges are in the single constraint above
    optional<z3::expr> edge_constraint_between(int, int) override { return nullopt; }
    void print_model() override {
        // A node's color is its smallest color in C
        for (int i = 1; i <= num_nodes; i++) {
            int color = 0;
            for (int c = 1; c <= K && color == 0; c++) {
                if (value(member(pair(i, c), *coloring)).is_true()) color = c;
            }
            cout << "node_" << i << ": " << color << " ";
        }
    }
};

}  // namespace

void register_sets(Z3Registry& registry) {
    registry.add_generic("SET-CUBE", "INT", make_generic<SetCubeColorer>());
    registry.add_generic("SET-MASK", "INT", make_generic<SetMaskColorer>());
    registry.add_generic("SET-MEM", "INT", make_generic<SetMemberColorer>());
    registry.add_generic("SET-CLASSES", "INT", make_generic<SetClassesColorer>());
    registry.add_generic("REL-JOIN", "INT", make_generic<RelJoinColorer>());
}
