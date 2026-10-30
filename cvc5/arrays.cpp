// Array encodings: ARR-MAP, and the Sebastiani chains ARR-EXP, ARR-INL over any element theory
#include "colorer.h"
#include "elements.h"
#include "registry.h"

namespace {

// ============================================================================
// THEORY OF ARRAYS (Global Mapped Index - The "Glorified LIA" Cube)
// ============================================================================
class ArrayMappedColorer : public AbstractGraphColorer {
private:
    cvc5::Term global_array;
    vector<cvc5::Term> idx_vars;
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver.setLogic("QF_ALIA"); }
    
    void build_variables_and_bounds() override {
        cvc5::Sort int_sort = tm.getIntegerSort();
        cvc5::Sort array_sort = tm.mkArraySort(int_sort, int_sort);
        
        // One single array for the entire graph
        global_array = tm.mkConst(array_sort, "GlobalColors");
        
        // Initialize the array mapping: A[c] = c for all c in 1..K
        for (int c = 1; c <= K; c++) {
            cvc5::Term c_term = tm.mkInteger(c);
            cvc5::Term read_c = tm.mkTerm(cvc5::Kind::SELECT, {global_array, c_term});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {read_c, c_term}));
        }
        
        cvc5::Term one = tm.mkInteger(1);
        cvc5::Term k_term = tm.mkInteger(K);
        idx_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            // The node's chosen index is bounded 1 <= idx <= K (Pure LIA logic)
            idx_vars[i] = tm.mkConst(int_sort, "idx_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {idx_vars[i], one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {idx_vars[i], k_term}));
            
            // The node's color is retrieved by passing the bounded index into the Array
            node_vars[i] = tm.mkTerm(cvc5::Kind::SELECT, {global_array, idx_vars[i]});
        }
    }
    
    void print_model() override {
        AbstractGraphColorer::print_model();
        for (int i = 1; i <= num_nodes; i++) {
            cout << "idx_" << i << ": " << solver.getValue(idx_vars[i]).toString() << " ";
        }
    }
};

// ============================================================================
// THEORY OF ARRAYS (Sebastiani array chain, any element theory)
// ============================================================================
// Indices and stored values are K distinct elements e_1..e_K:
//   A_{j+1} = store(A_j, i_j, e_j)   for j = 1..K, i_1 free and i_j = e_j otherwise
// and the node is A_{K+1}[i_1]: e_j if i_1 = e_j for some j >= 2, otherwise e_1
// (e_1 itself is a value of i_1 outside {e_2, ..., e_K}, so all K colors occur).
// ARR-EXP names every A_j with an explicit equation; ARR-INL nests the stores.
class ArrayChainColorer : public ElementGenericColorer {
private:
    bool inline_chain;
    vector<cvc5::Term> i1_vars;
public:
    ArrayChainColorer(int k, bool model, bool print, unique_ptr<ElementTheory> elements, bool inline_chain)
        : ElementGenericColorer(k, model, print, std::move(elements)), inline_chain(inline_chain) {}
protected:
    string container_logic() const override { return "A"; }
    void build_variables_and_bounds() override {
        ElementDomain domain = make_domain(K);
        cvc5::Sort array_sort = tm.mkArraySort(domain.sort, domain.sort);
        i1_vars.resize(num_nodes + 1);

        for (int i = 1; i <= num_nodes; i++) {
            // The free index i_1 (acts as the color selector)
            i1_vars[i] = tm.mkConst(domain.sort, "i_1_" + to_string(i));
            // A_1 (the uninitialized base array)
            cvc5::Term current_A = tm.mkConst(array_sort, "A_1_" + to_string(i));

            for (int j = 1; j <= K; j++) {
                cvc5::Term index_j = (j == 1) ? i1_vars[i] : domain.elements[j - 1];
                cvc5::Term store_op = tm.mkTerm(cvc5::Kind::STORE, {current_A, index_j, domain.elements[j - 1]});
                if (inline_chain) {
                    current_A = store_op;
                } else {
                    // A_{j+1} = A_j[ i_j -> e_j ]
                    cvc5::Term next_A = tm.mkConst(array_sort, "A_" + to_string(j + 1) + "_" + to_string(i));
                    solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {next_A, store_op}));
                    current_A = next_A;
                }
            }

            // v_i = A_{K+1}[i_1]
            node_vars[i] = tm.mkTerm(cvc5::Kind::SELECT, {current_A, i1_vars[i]});
        }
    }

    void print_model() override {
        AbstractGraphColorer::print_model();
        for (int i = 1; i <= num_nodes; i++) {
            cout << "i_1_" << i << ": " << solver.getValue(i1_vars[i]).toString() << " ";
        }
    }
};

}  // namespace

void register_arrays(Registry& registry) {
    registry.add("ARR-MAP", make<ArrayMappedColorer>());
    registry.add_generic("ARR-EXP", "INT", make_generic<ArrayChainColorer>(false));
    registry.add_generic("ARR-INL", "INT", make_generic<ArrayChainColorer>(true));
}
