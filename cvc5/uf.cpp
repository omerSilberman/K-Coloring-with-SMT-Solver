// Uninterpreted-function encodings: LIST-UF, UF, UF-CARD, and OR over any element theory
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// ============================================================================
// THEORY OF LISTS (Uninterpreted Functions)
// ============================================================================
class ListUfColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UF"); }
    void build_variables_and_bounds() override {
        cvc5::Sort list_sort = tm.mkUninterpretedSort("List");
        cvc5::Term nil_val = tm.mkConst(list_sort, "nil");
        cvc5::Sort cons_sig = tm.mkFunctionSort({list_sort, list_sort}, list_sort);
        cvc5::Term cons_func = tm.mkConst(cons_sig, "cons");
        
        cvc5::Term current_color = tm.mkTerm(cvc5::Kind::APPLY_UF, {cons_func, nil_val, nil_val});
        color_constants.push_back(current_color);
        for (int i = 1; i < K; i++) {
            current_color = tm.mkTerm(cvc5::Kind::APPLY_UF, {cons_func, current_color, nil_val});
            color_constants.push_back(current_color);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {color_constants[i], color_constants[j]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq}));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(list_sort, "node_" + to_string(i));
            cvc5::Term domain_constraint = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[0]});
            for (int c = 1; c < K; c++) {
                cvc5::Term is_color_c = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[c]});
                domain_constraint = tm.mkTerm(cvc5::Kind::OR, {domain_constraint, is_color_c});
            }
            solver.assertFormula(domain_constraint);
        }
    }
};

// ============================================================================
// SIMPLE UNINTERPRETED FUNCTIONS
// ============================================================================
class UfColorer : public AbstractGraphColorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UF"); }
    void build_variables_and_bounds() override {
        cvc5::Sort color_sort = tm.mkUninterpretedSort("Color");
        for (int i = 1; i <= K; i++) {
            cvc5::Term color_const = tm.mkConst(color_sort, "C" + to_string(i));
            color_constants.push_back(color_const);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {color_constants[i], color_constants[j]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq}));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(color_sort, "node_" + to_string(i));
            cvc5::Term domain_constraint = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[0]});
            for (int c = 1; c < K; c++) {
                cvc5::Term is_color_c = tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], color_constants[c]});
                domain_constraint = tm.mkTerm(cvc5::Kind::OR, {domain_constraint, is_color_c});
            }
            solver.assertFormula(domain_constraint);
        }
    }
};

// ============================================================================
// UNINTERPRETED SORT WITH A CARDINALITY CONSTRAINT
// ============================================================================
// Nodes are constants of an uninterpreted sort Color, edges are u != v, and the
// only other assertion is (_ fmf.card Color K): Color has at most K elements.
// There are no colors and no domain constraint: the sort's size is the domain.
// cvc5's cardinality solver (Reynolds et al.) keeps the equivalence classes of Color
// terms in "regions" of its disequality graph and must merge them down to at most K
// classes without merging two disequal terms - which is K-coloring the graph. It
// splits on merging two classes and reports a conflict when it finds a (K+1)-clique.
// (Its other modes, --uf-ss=no-minimal/none, only work with quantifier model finding
// and answer UNKNOWN here, so cvc5's default is used.)
class UfCardColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_UFC"); }  // C: cardinality constraints
    void build_variables_and_bounds() override {
        cvc5::Sort color_sort = tm.mkUninterpretedSort("Color");
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(color_sort, "node_" + to_string(i));
        }
        solver.assertFormula(tm.mkCardinalityConstraint(color_sort, K));
    }
};

// ============================================================================
// DISJUNCTION OVER K ELEMENTS (any element theory)
// ============================================================================
// x = e_1 or ... or e_K for K distinct elements. UF, STRING and LIST-DT are this
// encoding with a fixed element theory; OR-<ELEM> runs it with any.
class OrColorer : public ElementGenericColorer {
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            vector<cvc5::Term> choices;
            for (const auto& e : domain.elements) {
                choices.push_back(tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], e}));
            }
            solver.assertFormula((K == 1) ? choices[0] : tm.mkTerm(cvc5::Kind::OR, choices));
        }
    }
};

}  // namespace

void register_uf(Registry& registry) {
    registry.add("LIST-UF", make<ListUfColorer>());
    registry.add("UF", make<UfColorer>());
    registry.add("UF-CARD", make<UfCardColorer>());
    registry.add_generic("OR", "UF", make_generic<OrColorer>());
}
