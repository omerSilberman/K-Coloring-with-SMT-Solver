// String encodings: STRING, STR-LEX, STR-INT, STR-REG, STR-SUB
#include "colorer.h"
#include "../common/strings.h"
#include "registry.h"

namespace {

// ============================================================================
// THEORY OF STRINGS (Original OR-Disjunction)
// ============================================================================
class StringColorer : public Cvc5Colorer {
private:
    vector<cvc5::Term> color_constants;
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_S"); }
    void build_variables_and_bounds() override {
        cvc5::Sort str_sort = tm.getStringSort();
        for (int i = 1; i <= K; i++) {
            string color_name = int_to_alpha(i);
            cvc5::Term color_const = tm.mkString(color_name);
            color_constants.push_back(color_const);
        }
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) {
                cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {color_constants[i], color_constants[j]});
                solver.assertFormula(tm.mkTerm(cvc5::Kind::NOT, {eq}));
            }
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
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
// THEORY OF STRINGS (Lexicographical Boundaries Cube)
// ============================================================================
class StringLexColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_SLIA"); }
    void build_variables_and_bounds() override {
        if (K > 50) {
            throw runtime_error("STR-LEX only supports K <= 50 due to ASCII printable contiguity.");
        }
        cvc5::Sort str_sort = tm.getStringSort();
        cvc5::Term len_one = tm.mkInteger(1);
        
        string start_char(1, 'A');
        string end_char(1, (char)('A' + K - 1));
        cvc5::Term start_term = tm.mkString(start_char);
        cvc5::Term end_term = tm.mkString(end_char);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            
            cvc5::Term len = tm.mkTerm(cvc5::Kind::STRING_LENGTH, {node_vars[i]});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {len, len_one}));
            
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_LEQ, {start_term, node_vars[i]}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_LEQ, {node_vars[i], end_term}));
        }
    }
};

// ============================================================================
// THEORY OF STRINGS (String-To-Int Projection Cube)
// ============================================================================
class StringIntColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_SLIA"); }
    void build_variables_and_bounds() override {
        cvc5::Sort str_sort = tm.getStringSort();
        cvc5::Term one = tm.mkInteger(1);
        cvc5::Term k_term = tm.mkInteger(K);

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            
            // Native String-to-Int Mapping!
            cvc5::Term node_as_int = tm.mkTerm(cvc5::Kind::STRING_TO_INT, {node_vars[i]});
            
            solver.assertFormula(tm.mkTerm(cvc5::Kind::GEQ, {node_as_int, one}));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::LEQ, {node_as_int, k_term}));

            // Force the canonical spelling (no leading zeros), otherwise "2" and "02"
            // would be two different colors with the same integer value.
            // str.from_int returns a String, so this is a String = String equality.
            cvc5::Term canonical = tm.mkTerm(cvc5::Kind::STRING_FROM_INT, {node_as_int});
            solver.assertFormula(tm.mkTerm(cvc5::Kind::EQUAL, {node_vars[i], canonical}));
        }
    }
};

// ============================================================================
// THEORY OF STRINGS (Native Regex Set Cube)
// ============================================================================
class StringRegexColorer : public Cvc5Colorer {
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_S"); }
    void build_variables_and_bounds() override {
        cvc5::Sort str_sort = tm.getStringSort();
        
        // 1. Build the Regex options
        vector<cvc5::Term> regex_options;
        for (int i = 1; i <= K; i++) {
            string color_name = int_to_alpha(i);
            cvc5::Term str_const = tm.mkString(color_name);
            // Convert literal string to a regex match
            cvc5::Term str_re = tm.mkTerm(cvc5::Kind::STRING_TO_REGEXP, {str_const});
            regex_options.push_back(str_re);
        }
        
        // 2. Unite them into a single Regular Language set
        cvc5::Term re_union;
        if (K == 1) {
            re_union = regex_options[0];
        } else {
            re_union = tm.mkTerm(cvc5::Kind::REGEXP_UNION, regex_options);
        }

        // 3. Constrain nodes natively to the Regex Language!
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_IN_REGEXP, {node_vars[i], re_union}));
        }
    }
};

// ============================================================================
// THEORY OF STRINGS (Substrings of a word with exactly K distinct substrings)
// ============================================================================
class StringSubstringColorer : public Cvc5Colorer {
private:
    string word;
public:
    using Cvc5Colorer::Cvc5Colorer;
protected:
    void configure_theory() override { solver.setLogic("QF_S"); }
    void build_variables_and_bounds() override {
        word = substring_word(K);
        cvc5::Sort str_sort = tm.getStringSort();
        cvc5::Term word_term = tm.mkString(word);

        // Every node is one of the K distinct substrings of the word (the empty string included)
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = tm.mkConst(str_sort, "node_" + to_string(i));
            solver.assertFormula(tm.mkTerm(cvc5::Kind::STRING_CONTAINS, {word_term, node_vars[i]}));
        }
    }
    void print_model() override {
        Cvc5Colorer::print_model();
        cout << "word: \"" << word << "\"";
    }
};

}  // namespace

void register_strings(Cvc5Registry& registry) {
    registry.add("STRING", make<StringColorer>());
    registry.add("STR-LEX", make<StringLexColorer>());
    registry.add("STR-INT", make<StringIntColorer>());
    registry.add("STR-REG", make<StringRegexColorer>());
    registry.add("STR-SUB", make<StringSubstringColorer>());
}
