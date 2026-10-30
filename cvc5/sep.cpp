// Separation-logic encoding: SEP, over any element theory
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// ============================================================================
// SEPARATION LOGIC (Colors are heap cells, any element theory)
// ============================================================================
// Locations and data both have the element sort; the data stored is the element
// e_1. The element theory is asked for K + 1 elements only so that the sort is known
// to hold K locations plus sep.nil, which is never allocated (the elements
// themselves are not used as locations).
// The heap is exactly K cells, c_1 |-> e_1 * ... * c_K |-> e_1, where * (separating
// conjunction) forces the cells to be distinct. Each node is a pointer into that
// heap: (x |-> e_1) * true. Edges are not disequalities but (u |-> e_1) * (v |-> e_1)
// * true: u and v point to two disjoint cells, which is the same thing as different colors.
class SepColorer : public ElementGenericColorer {
private:
    cvc5::Term data;
    cvc5::Term star(const vector<cvc5::Term>& parts) {
        return (parts.size() == 1) ? parts[0] : tm.mkTerm(cvc5::Kind::SEP_STAR, parts);
    }
    cvc5::Term points_to(const cvc5::Term& loc) {
        return tm.mkTerm(cvc5::Kind::SEP_PTO, {loc, data});
    }
public:
    using ElementGenericColorer::ElementGenericColorer;
protected:
    void configure_theory() override {
        solver.setOption("incremental", "false");  // cvc5 requires this for separation logic
        solver.setLogic("ALL");
    }
    void build_variables_and_bounds() override {
        // The heap must be declared before the first assertion
        ElementDomain domain = element_theory->make_domain(tm, K + 1);
        solver.declareSepHeap(domain.sort, domain.sort);
        assert_constraints(domain);
        data = domain.elements[0];

        vector<cvc5::Term> cells;
        for (int c = 1; c <= K; c++) {
            cells.push_back(points_to(tm.mkConst(domain.sort, "c_" + to_string(c))));
        }
        solver.assertFormula(star(cells));

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(domain.sort, "node_" + to_string(i));
            solver.assertFormula(star({points_to(node_vars[i]), tm.mkTrue()}));
        }
    }
    cvc5::Term edge_constraint(const cvc5::Term& u, const cvc5::Term& v) override {
        return star({points_to(u), points_to(v), tm.mkTrue()});
    }
};

}  // namespace

void register_sep(Registry& registry) {
    registry.add_generic("SEP", "UF", make_generic<SepColorer>());
}
