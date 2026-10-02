#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/smt.h"
#include "smt-switch/datatype.h"

using namespace smt;
using namespace std;

// ============================================================================
// 1. ABSTRACT BASE CLASS
// Handles all shared logic: Parsing, Edge Constraints, and Execution
// ============================================================================
class AbstractGraphColorer {
protected:
    int num_nodes = 0;
    int num_edges = 0;
    int K;
    bool produce_model;
    
    vector<pair<int, int>> edges;
    SmtSolver solver;
    vector<Term> node_vars;

public:
    AbstractGraphColorer(int k, bool model) : K(k), produce_model(model) {
        // Initialize the backend solver here (shared for all theories)
        solver = Cvc5SolverFactory::create(false);
        if (produce_model) {
            solver->set_opt("produce-models", "true");
        }
    }

    virtual ~AbstractGraphColorer() = default;

    // SHARED: Read DIMACS graph
    void load_dimacs(const string& filename) {
        ifstream infile(filename);
        if (!infile.is_open()) {
            throw runtime_error("Could not open file: " + filename);
        }

        string line;
        while (getline(infile, line)) {
            if (line.empty() || line[0] == 'c') continue;
            if (line[0] == 'p') {
                string p, edge;
                stringstream ss(line);
                ss >> p >> edge >> num_nodes >> num_edges;
            } else if (line[0] == 'e') {
                char e;
                int u, v;
                stringstream ss(line);
                ss >> e >> u >> v;
                edges.push_back({u, v});
            }
        }
        // Resize array to hold 1-indexed node variables
        node_vars.resize(num_nodes + 1);
    }

    // SHARED: The universal execution pipeline
    void solve() {
        configure_theory();              // 1. Let subclass set QF_LIA or QF_BV
        build_variables_and_bounds();    // 2. Let subclass create variables & bounds
        build_universal_edge_constraints(); // 3. Base class builds u != v

        Result res = solver->check_sat();

        if (res.is_sat()) {
            cout << "SAT" << endl;
            if (produce_model) {
                cout << "MODEL: ";
                for (int i = 1; i <= num_nodes; i++) {
                    print_node_value(i); // 4. Let subclass print format
                }
                cout << endl;
            }
        } else if (res.is_unsat()) {
            cout << "UNSAT" << endl;
        } else {
            cout << "UNKNOWN" << endl;
        }
    }

protected:
    // PURE VIRTUALS: These must be implemented by the specific theories
    virtual void configure_theory() = 0;
    virtual void build_variables_and_bounds() = 0;
    virtual void print_node_value(int node_idx) = 0;

private:
    // SHARED LOGIC: Regardless of theory, node_u != node_v uses the same SMT syntax!
    void build_universal_edge_constraints() {
        for (const auto& edge : edges) {
            Term u_eq_v = solver->make_term(Equal, node_vars[edge.first], node_vars[edge.second]);
            Term u_neq_v = solver->make_term(Not, u_eq_v);
            solver->assert_formula(u_neq_v);
        }
    }
};

// ============================================================================
// 2. LINEAR INTEGER ARITHMETIC (LIA) IMPLEMENTATION
// ============================================================================
class LiaColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override {
        solver->set_logic("QF_LIA");
    }

    void build_variables_and_bounds() override {
        Sort int_sort = solver->make_sort(INT);
        Term one = solver->make_term("1", int_sort);
        Term k_term = solver->make_term(to_string(K), int_sort);

        for (int i = 1; i <= num_nodes; ++i) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), int_sort);
            // 1 <= node
            solver->assert_formula(solver->make_term(Ge, node_vars[i], one));
            // node <= K
            solver->assert_formula(solver->make_term(Le, node_vars[i], k_term));
        }
    }

    void print_node_value(int node_idx) override {
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 3. BIT-VECTOR (BV) IMPLEMENTATION
// ============================================================================
class BvColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override {
        solver->set_logic("QF_BV");
    }

    void build_variables_and_bounds() override {
        int width = 1;
        while ((1 << width) - 1 < K) {
            width++;
        }
        
        Sort bv_sort = solver->make_sort(BV, width);
        Term one = solver->make_term(to_string(1), bv_sort, 10);
        Term k_term = solver->make_term(to_string(K), bv_sort, 10);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), bv_sort);
            // 1 <= node (Unsigned BV)
            solver->assert_formula(solver->make_term(BVUge, node_vars[i], one));
            // node <= K (Unsigned BV)
            solver->assert_formula(solver->make_term(BVUle, node_vars[i], k_term));
        }
    }

    void print_node_value(int node_idx) override {
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// NON-LINEAR REAL ARITHMETIC (NLRA) IMPLEMENTATION
// ============================================================================
class NlraColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override {
        // QF_NRA: Quantifier-Free Non-Linear Real Arithmetic
        solver->set_logic("QF_NRA"); 
    }

    void build_variables_and_bounds() override {
        Sort real_sort = solver->make_sort(REAL);
        Term zero = solver->make_term("0", real_sort);

        for (int i = 1; i <= num_nodes; i++) {
            // 1. Declare the node as a continuous Real variable
            node_vars[i] = solver->make_symbol("node_" + to_string(i), real_sort);
            
            // 2. Create a vector to hold all our (node - c) terms
            vector<Term> roots;
            
            // 3. Generate all roots
            for (int c = 1; c <= K; c++) {
                Term c_term = solver->make_term(to_string(c), real_sort);
                Term diff = solver->make_term(Minus, node_vars[i], c_term);
                roots.push_back(diff);
            }
            
            // 4. Multiply them ALL together at once (n-ary multiplication)
            Term polynomial = solver->make_term(Mult, roots);
            
            // 5. Assert that the flat polynomial equals 0
            Term eq_zero = solver->make_term(Equal, polynomial, zero);
            solver->assert_formula(eq_zero);
        }
    }

    void print_node_value(int node_idx) override {
        // CVC5 may print reals as fractions (e.g., "1/1"), which is fine for our model!
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 6. THEORY OF LISTS (Uninterpreted Functions simulating Cons structures)
// ============================================================================
class ListUfColorer : public AbstractGraphColorer {
private:
    vector<Term> color_constants;

public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override {
        // QF_UF: Quantifier-Free Uninterpreted Functions
        solver->set_logic("QF_UF"); 
    }

    void build_variables_and_bounds() override {
        // FIX: Explicitly set arity to 0 to define a brand new root type
        Sort list_sort = solver->make_sort("List", 0);
        Term nil_val = solver->make_symbol("nil", list_sort);
        
        // Define the 'cons' function: cons(List, List) -> List
        Sort cons_sig = solver->make_sort(FUNCTION, {list_sort, list_sort, list_sort});
        Term cons_func = solver->make_symbol("cons", cons_sig);
        
        // Generate the K distinct structural colors
        // C1 = cons(nil, nil)
        Term current_color = solver->make_term(Apply, cons_func, nil_val, nil_val);
        color_constants.push_back(current_color);
        
        // C2 = cons(C1, nil), C3 = cons(C2, nil), etc.
        for (int i = 1; i < K; i++) {
            current_color = solver->make_term(Apply, cons_func, current_color, nil_val);
            color_constants.push_back(current_color);
        }
        
        // Force the colors to be pairwise distinct 
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                Term eq = solver->make_term(Equal, color_constants[i], color_constants[j]);
                Term neq = solver->make_term(Not, eq);
                solver->assert_formula(neq);
            }
        }

        // Create node variables and force them into the List domain using OR
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), list_sort);
            
            // Build the boolean OR: node == C1 OR node == C2 OR ...
            Term domain_constraint = solver->make_term(Equal, node_vars[i], color_constants[0]);
            for (int c = 1; c < K; c++) {
                Term is_color_c = solver->make_term(Equal, node_vars[i], color_constants[c]);
                domain_constraint = solver->make_term(Or, domain_constraint, is_color_c);
            }
            solver->assert_formula(domain_constraint);
        }
    }

    void print_node_value(int node_idx) override {
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 6. TRUE THEORY OF LISTS (NATIVE DATATYPES)
// ============================================================================
// ============================================================================
// 6. TRUE THEORY OF DATATYPES (Flat Enum to bypass smt-switch recursion bug)
// ============================================================================
class ListDtColorer : public AbstractGraphColorer {
private:
    vector<Term> color_constants;

public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override {
        // QF_DT: Quantifier-Free Datatypes
        solver->set_logic("QF_DT"); 
    }

    void build_variables_and_bounds() override {
        // 1. Create a Datatype declaration for our Colors
        DatatypeDecl color_decl = solver->make_datatype_decl("Color");
        
        // 2. Generate K distinct native constructors (C1, C2, ... CK)
        // These take no arguments, so there is NO recursion and NO crash!
        for (int i = 1; i <= K; i++) {
            DatatypeConstructorDecl c = solver->make_datatype_constructor_decl("C" + to_string(i));
            solver->add_constructor(color_decl, c);
        }
        
        // 3. Finalize the Datatype
        Sort color_sort = solver->make_datatype_sort(color_decl);

        // 4. Retrieve the actual constructor Terms and instantiate them
        for (int i = 1; i <= K; i++) {
            Term op = solver->get_constructor(color_sort, "C" + to_string(i));
            // Apply the constructor (it takes 0 arguments)
            color_constants.push_back(solver->make_term(Apply_Constructor, op));
        }
        
        // NOTICE: We STILL don't need manual C1 != C2 assertions!
        // QF_DT inherently knows that Datatype constructors are strictly distinct.

        // 5. Create node variables and force them into the Datatype domain
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), color_sort);
            
            Term domain_constraint = solver->make_term(Equal, node_vars[i], color_constants[0]);
            for (int c = 1; c < K; c++) {
                Term is_color_c = solver->make_term(Equal, node_vars[i], color_constants[c]);
                domain_constraint = solver->make_term(Or, domain_constraint, is_color_c);
            }
            solver->assert_formula(domain_constraint);
        }
    }

    void print_node_value(int node_idx) override {
        // This will print the native Datatype enum values (e.g., C1, C2)
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 7. SIMPLE UNINTERPRETED FUNCTIONS (Flat Constants)
// ============================================================================
class UfColorer : public AbstractGraphColorer {
private:
    vector<Term> color_constants;

public:
    using AbstractGraphColorer::AbstractGraphColorer;

protected:
    void configure_theory() override {
        // QF_UF: Quantifier-Free Uninterpreted Functions
        solver->set_logic("QF_UF"); 
    }

    void build_variables_and_bounds() override {
        // 1. Declare a brand new, empty, uninterpreted sort named "Color"
        Sort color_sort = solver->make_sort("Color", 0);
        
        // 2. Generate K distinct uninterpreted constants
        for (int i = 1; i <= K; i++) {
            Term color_const = solver->make_symbol("C" + to_string(i), color_sort);
            color_constants.push_back(color_const);
        }
        
        // 3. CRITICAL: Force the constants to be pairwise distinct
        // Without this, the UF solver will cheat and make C1 == C2 to easily color the graph!
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                Term eq = solver->make_term(Equal, color_constants[i], color_constants[j]);
                Term neq = solver->make_term(Not, eq);
                solver->assert_formula(neq);
            }
        }

        // 4. Create node variables and force them into our K constants
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), color_sort);
            
            Term domain_constraint = solver->make_term(Equal, node_vars[i], color_constants[0]);
            for (int c = 1; c < K; c++) {
                Term is_color_c = solver->make_term(Equal, node_vars[i], color_constants[c]);
                domain_constraint = solver->make_term(Or, domain_constraint, is_color_c);
            }
            solver->assert_formula(domain_constraint);
        }
    }

    void print_node_value(int node_idx) override {
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 8. THEORY OF STRINGS (Original OR-Disjunction)
// ============================================================================
class StringColorer : public AbstractGraphColorer {
private:
    vector<Term> color_constants;
    string int_to_alpha(int n) {
        string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        string result = "";
        while (n > 0) {
            n--;
            result = chars[n % 52] + result;
            n /= 52;
        }
        return result;
    }
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override { solver->set_logic("QF_S"); }
    void build_variables_and_bounds() override {
        Sort str_sort = solver->make_sort(STRING);
        for (int i = 1; i <= K; i++) {
            string color_name = int_to_alpha(i);
            Term color_const = solver->make_symbol(color_name, str_sort);
            color_constants.push_back(color_const);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                Term eq = solver->make_term(Equal, color_constants[i], color_constants[j]);
                solver->assert_formula(solver->make_term(Not, eq));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), str_sort);
            Term domain_constraint = solver->make_term(Equal, node_vars[i], color_constants[0]);
            for (int c = 1; c < K; c++) {
                Term is_color_c = solver->make_term(Equal, node_vars[i], color_constants[c]);
                domain_constraint = solver->make_term(Or, domain_constraint, is_color_c);
            }
            solver->assert_formula(domain_constraint);
        }
    }
    void print_node_value(int node_idx) override {
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 10. THEORY OF STRINGS (Lexicographical Boundaries Cube)
// ============================================================================
class StringLexColorer : public AbstractGraphColorer {
public:
    using AbstractGraphColorer::AbstractGraphColorer;
protected:
    void configure_theory() override {
        solver->set_logic("QF_SLIA"); // Requires LIA for the length check
    }
    void build_variables_and_bounds() override {
        if (K > 50) {
            throw runtime_error("STR-LEX only supports K <= 50 due to ASCII printable contiguity.");
        }

        Sort str_sort = solver->make_sort(STRING);
        Sort int_sort = solver->make_sort(INT);
        Term len_one = solver->make_term("1", int_sort);
        
        // Boundaries based on ASCII ('A' is 65)
        string start_char(1, 'A');
        string end_char(1, (char)('A' + K - 1));
        
        // FIX: Added 'false' to trigger the correct string literal function overload
        Term start_term = solver->make_term(start_char, false, str_sort);
        Term end_term = solver->make_term(end_char, false, str_sort);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = solver->make_symbol("node_" + to_string(i), str_sort);
            
            // 1. Force the string to be exactly 1 character long
            Term len = solver->make_term(StrLen, node_vars[i]);
            solver->assert_formula(solver->make_term(Equal, len, len_one));
            
            // 2. Lexicographical bounds: "A" <= node <= "EndChar"
            solver->assert_formula(solver->make_term(StrLeq, start_term, node_vars[i]));
            solver->assert_formula(solver->make_term(StrLeq, node_vars[i], end_term));
        }
    }
    void print_node_value(int node_idx) override {
        cout << solver->get_value(node_vars[node_idx])->to_string() << " ";
    }
};

// ============================================================================
// 7. MAIN ENTRY POINT (FACTORY / ROUTER)
// ============================================================================
int main(int argc, char** argv) {
    if (argc < 4) {
        cerr << "Usage: ./smt_solver <LIA|BV|NLRA|LIST-UF> <dimacs_file> <K> [--model]" << endl;
        return 1;
    }

    string theory = argv[1];
    string filename = argv[2];
    int K = stoi(argv[3]);
    bool produce_model = (argc >= 5 && string(argv[4]) == "--model");

    try {
        AbstractGraphColorer* colorer = nullptr;

        // Route to the correct OOP subclass
        if (theory == "LIA") {
            colorer = new LiaColorer(K, produce_model);
        } else if (theory == "BV") {
            colorer = new BvColorer(K, produce_model);
        } else if (theory == "NLRA") {
            colorer = new NlraColorer(K, produce_model);
        } else if (theory == "LIST-UF") {
            colorer = new ListUfColorer(K, produce_model);
        } else if (theory == "LIST-DT") {
            colorer = new ListDtColorer(K, produce_model);
        } else if (theory == "UF") {
            colorer = new UfColorer(K, produce_model);
        } else if (theory == "STRING") {
            colorer = new StringColorer(K, produce_model); 
        } else if (theory == "STR-LEX") {
            colorer = new StringLexColorer(K, produce_model); 
        } else {
            cerr << "Error: Unknown theory '" << theory << "'." << endl;
            return 1;
        }

        colorer->load_dimacs(filename);
        colorer->solve();

        delete colorer;
    } catch (const exception& e) {
        cerr << "Exception caught: " << e.what() << endl;
        return 1;
    }

    return 0;
}