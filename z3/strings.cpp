// String encodings: STRING, STR-LEX, STR-INT, STR-REG, STR-SUB (see cvc5/strings.cpp and the README)
#include "colorer.h"
#include "../common/strings.h"
#include "registry.h"

namespace {

// x equals one of K distinct literals "A", "B", ...
class StringColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_S"); }
    void build_variables_and_bounds() override {
        vector<z3::expr> colors;
        for (int i = 1; i <= K; i++) colors.push_back(ctx.string_val(int_to_alpha(i)));
        for (int i = 0; i < K; i++) {
            for (int j = i + 1; j < K; j++) solver.add(!(colors[i] == colors[j]));
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.string_sort());
            z3::expr domain = (node_vars[i] == colors[0]);
            for (int c = 1; c < K; c++) domain = domain || (node_vars[i] == colors[c]);
            solver.add(domain);
        }
    }
};

// len(x) = 1 and "A" <= x <= chr('A' + K - 1) lexicographically (K <= 50)
class StringLexColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_SLIA"); }
    void build_variables_and_bounds() override {
        if (K > 50) {
            throw runtime_error("STR-LEX only supports K <= 50 due to ASCII printable contiguity.");
        }
        z3::expr start = ctx.string_val(string(1, 'A'));
        z3::expr end = ctx.string_val(string(1, (char)('A' + K - 1)));
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.string_sort());
            solver.add(node_vars[i].length() == 1);
            solver.add(lex_leq(start, node_vars[i]));
            solver.add(lex_leq(node_vars[i], end));
        }
    }
    // str.<= (the C++ API has no operator for it)
    z3::expr lex_leq(const z3::expr& a, const z3::expr& b) {
        Z3_ast r = Z3_mk_str_le(ctx, a, b);
        ctx.check_error();
        return z3::expr(ctx, r);
    }
};

// 1 <= str.to_int(x) <= K, and x = str.from_int(str.to_int(x)) (canonical spelling)
class StringIntColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_SLIA"); }
    void build_variables_and_bounds() override {
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.string_sort());
            z3::expr as_int = node_vars[i].stoi();
            solver.add(as_int >= 1);
            solver.add(as_int <= K);
            solver.add(node_vars[i] == as_int.itos());
        }
    }
};

// x in ("A" | "B" | ...): membership in a union regex of K literals
class StringRegexColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_S"); }
    void build_variables_and_bounds() override {
        vector<Z3_ast> options;
        vector<z3::expr> keep;  // keeps the terms alive while their raw handles are used
        for (int i = 1; i <= K; i++) {
            keep.push_back(z3::to_re(ctx.string_val(int_to_alpha(i))));
            options.push_back(keep.back());
        }
        z3::expr re_union = keep[0];
        if (K > 1) {
            Z3_ast r = Z3_mk_re_union(ctx, options.size(), options.data());
            ctx.check_error();
            re_union = z3::expr(ctx, r);
        }
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.string_sort());
            solver.add(z3::in_re(node_vars[i], re_union));
        }
    }
};

// str.contains(W, x), where W has exactly K distinct substrings
class StringSubstringColorer : public Z3Colorer {
private:
    string word;
public:
    using Z3Colorer::Z3Colorer;
protected:
    void configure_theory() override { set_logic("QF_S"); }
    void build_variables_and_bounds() override {
        word = substring_word(K);
        z3::expr word_term = ctx.string_val(word);
        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), ctx.string_sort());
            solver.add(word_term.contains(node_vars[i]));
        }
    }
    void print_model() override {
        Z3Colorer::print_model();
        cout << "word: \"" << word << "\"";
    }
};

}  // namespace

void register_strings(Z3Registry& registry) {
    registry.add("STRING", make<StringColorer>());
    registry.add("STR-LEX", make<StringLexColorer>());
    registry.add("STR-INT", make<StringIntColorer>());
    registry.add("STR-REG", make<StringRegexColorer>());
    registry.add("STR-SUB", make<StringSubstringColorer>());
}
