// Uninterpreted-function encodings: LIST-UF, UF, UF-CARD, and OR over any element theory
// (see cvc5/uf.cpp and the README)
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// node = c_1 or ... or node = c_K, written as a left-nested OR (as in the cvc5 version)
z3::expr is_one_of(const z3::expr& x, const vector<z3::expr>& colors) {
    z3::expr domain = (x == colors[0]);
    for (size_t c = 1; c < colors.size(); c++) domain = domain || (x == colors[c]);
    return domain;
}

// The colors are cons(nil, nil), cons(cons(nil, nil), nil), ... over an uninterpreted
// List sort, asserted pairwise distinct
class ListUfColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_UF"); }
    void build_variables_and_bounds() override {
        z3::sort list_sort = ctx.uninterpreted_sort("List");
        z3::expr nil_val = constant("nil", list_sort);
        z3::func_decl cons = ctx.function("cons", list_sort, list_sort, list_sort);

        vector<z3::expr> colors{cons(nil_val, nil_val)};
        for (int i = 1; i < K; i++) colors.push_back(cons(colors.back(), nil_val));
        this->colors = colors;
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) solver.add(!(colors[i] == colors[j]));
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), list_sort);
            solver.add(is_one_of(node_vars[i], colors));
        }
    }
};

// K pairwise-distinct constants C1..CK of an uninterpreted sort
class UfColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_UF"); }
    void build_variables_and_bounds() override {
        z3::sort color_sort = ctx.uninterpreted_sort("Color");
        vector<z3::expr> colors;
        for (int i = 1; i <= K; i++) colors.push_back(constant("C" + to_string(i), color_sort));
        this->colors = colors;
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) solver.add(!(colors[i] == colors[j]));
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), color_sort);
            solver.add(is_one_of(node_vars[i], colors));
        }
    }
};

// An uninterpreted sort with at most K elements. Z3 has no cardinality constraint
// (cvc5's fmf.card), so it is stated with a quantifier: K constants d_1..d_K, not
// necessarily distinct, and every element of Color is one of them:
//   forall x: Color. x = d_1 or ... or x = d_K
// Z3 solves this with model-based quantifier instantiation (MBQI) over finite models.
class UfCardColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("UF"); }  // quantified UF
    void build_variables_and_bounds() override {
        z3::sort color_sort = ctx.uninterpreted_sort("Color");
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), color_sort);
        }
        vector<z3::expr> representatives;
        for (int j = 1; j <= K; j++) representatives.push_back(constant("d_" + to_string(j), color_sort));
        z3::expr x = constant("x", color_sort);
        solver.add(z3::forall(x, is_one_of(x, representatives)));
    }
};

// x = e_1 or ... or e_K for K distinct elements of any element theory
class OrColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        colors = domain.elements;
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), domain.sort);
            vector<z3::expr> choices;
            for (const auto& e : domain.elements) choices.push_back(node_vars[i] == e);
            solver.add(any_of(choices));
        }
    }
};

}  // namespace

void register_uf(Z3Registry& registry) {
    registry.add("LIST-UF", make<ListUfColorer>());
    registry.add("UF", make<UfColorer>());
    registry.add("UF-CARD", make<UfCardColorer>());
    registry.add_generic("OR", "UF", make_generic<OrColorer>());
}
