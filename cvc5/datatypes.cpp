// Datatype encodings: LIST-DT, PEANO
#include "colorer.h"
#include "registry.h"

namespace {

// ============================================================================
// TRUE THEORY OF DATATYPES
// ============================================================================
class ListDtColorer : public Cvc5Colorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_DT"); }
    void build_variables_and_bounds() override {
        cvc5::DatatypeDecl color_decl = tm.mkDatatypeDecl("Color");
        for (int i = 1; i <= K; i++) {
            cvc5::DatatypeConstructorDecl c = tm.mkDatatypeConstructorDecl("C" + to_string(i));
            color_decl.addConstructor(c);
        }
        cvc5::Sort color_sort = tm.mkDatatypeSort(color_decl);
        cvc5::Datatype dt = color_sort.getDatatype();

        for (int i = 1; i <= K; i++) {
            cvc5::Term op = dt.getConstructor("C" + to_string(i)).getTerm();
            color_constants.push_back(tm.mkTerm(cvc5::Kind::APPLY_CONSTRUCTOR, {op}));
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
// DATATYPES (Peano naturals)
// ============================================================================
// Nat = Z | S(pred: Nat), and the colors are Z, S(Z), ..., S^(K-1)(Z). Instead of
// listing them, each node gets one clause saying x is not K successors deep:
//   not (is-S(x) and is-S(pred x) and ... and is-S(pred^(K-1) x))
// Once some pred^j x is Z, the later pred applications are unconstrained, but the
// conjunction is already false at j, so the clause holds exactly for depth < K.
class PeanoColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_DT"); }
    void build_variables_and_bounds() override {
        cvc5::DatatypeDecl nat_decl = tm.mkDatatypeDecl("Nat");
        nat_decl.addConstructor(tm.mkDatatypeConstructorDecl("Z"));
        cvc5::DatatypeConstructorDecl succ = tm.mkDatatypeConstructorDecl("S");
        succ.addSelectorSelf("pred");
        nat_decl.addConstructor(succ);
        cvc5::Sort nat_sort = tm.mkDatatypeSort(nat_decl);
        cvc5::DatatypeConstructor s_cons = nat_sort.getDatatype().getConstructor("S");
        cvc5::Term is_s = s_cons.getTesterTerm();
        cvc5::Term pred = s_cons.getSelector("pred").getTerm();

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(nat_sort, "node_" + to_string(i));
            vector<cvc5::Term> deep;
            cvc5::Term current = node_vars[i];
            for (int j = 0; j < K; j++) {
                deep.push_back(tm.mkTerm(cvc5::Kind::APPLY_TESTER, {is_s, current}));
                current = tm.mkTerm(cvc5::Kind::APPLY_SELECTOR, {pred, current});
            }
            cvc5::Term too_deep = (K == 1) ? deep[0] : tm.mkTerm(cvc5::Kind::AND, deep);
            solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {too_deep}));
        }
    }
};

}  // namespace

void register_datatypes(Cvc5Registry& registry) {
    registry.add("LIST-DT", make<ListDtColorer>());
    registry.add("PEANO", make<PeanoColorer>());
}
