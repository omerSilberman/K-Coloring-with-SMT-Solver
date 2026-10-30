// Array encodings: ARR-MAP, and the Sebastiani chains ARR-EXP, ARR-INL over any element
// theory (see cvc5/arrays.cpp and the README)
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// One global array with A[c] = c for c = 1..K; color x = A[idx] with 1 <= idx <= K
class ArrayMappedColorer : public Z3Colorer {
private:
    vector<z3::expr> idx_vars;
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_ALIA"); }
    void build_variables_and_bounds() override {
        z3::expr global_array = constant("GlobalColors", ctx.array_sort(ctx.int_sort(), ctx.int_sort()));
        for (int c = 1; c <= K; c++) solver.add(z3::select(global_array, c) == c);

        idx_vars.assign(num_nodes + 1, ctx.int_val(0));
        for (int i = 1; i <= num_nodes; i++) {
            idx_vars[i] = constant("idx_" + to_string(i), ctx.int_sort());
            solver.add(idx_vars[i] >= 1);
            solver.add(idx_vars[i] <= K);
            node_vars[i] = z3::select(global_array, idx_vars[i]);
        }
    }
    void print_model() override {
        Z3Colorer::print_model();
        for (int i = 1; i <= num_nodes; i++) {
            cout << "idx_" << i << ": " << value(idx_vars[i]).to_string() << " ";
        }
    }
};

// A_{j+1} = store(A_j, i_j, e_j) for j = 1..K, i_1 free and i_j = e_j otherwise; the node
// is A_{K+1}[i_1]. ARR-EXP names every A_j with an equation; ARR-INL nests the stores.
class ArrayChainColorer : public ElementGenericColorer {
private:
    bool inline_chain;
    vector<z3::expr> i1_vars;
public:
    ArrayChainColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements, bool inline_chain)
        : ElementGenericColorer(k, model, print, std::move(elements)), inline_chain(inline_chain) {}
protected:
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        z3::sort array_sort = ctx.array_sort(domain.sort, domain.sort);
        i1_vars.assign(num_nodes + 1, ctx.bool_val(false));

        for (int i = 1; i <= num_nodes; i++) {
            i1_vars[i] = constant("i_1_" + to_string(i), domain.sort);  // the color selector
            z3::expr current_A = constant("A_1_" + to_string(i), array_sort);
            for (int j = 1; j <= K; j++) {
                z3::expr index_j = (j == 1) ? i1_vars[i] : domain.elements[j - 1];
                z3::expr store_op = z3::store(current_A, index_j, domain.elements[j - 1]);
                if (inline_chain) {
                    current_A = store_op;
                } else {
                    z3::expr next_A = constant("A_" + to_string(j + 1) + "_" + to_string(i), array_sort);
                    solver.add(next_A == store_op);
                    current_A = next_A;
                }
            }
            node_vars[i] = z3::select(current_A, i1_vars[i]);
        }
    }
    void print_model() override {
        Z3Colorer::print_model();
        for (int i = 1; i <= num_nodes; i++) {
            cout << "i_1_" << i << ": " << value(i1_vars[i]).to_string() << " ";
        }
    }
};

}  // namespace

void register_arrays(Z3Registry& registry) {
    registry.add("ARR-MAP", make<ArrayMappedColorer>());
    registry.add_generic("ARR-EXP", "INT", make_generic<ArrayChainColorer>(false));
    registry.add_generic("ARR-INL", "INT", make_generic<ArrayChainColorer>(true));
}
