// Datatype encodings: LIST-DT, PEANO (see cvc5/datatypes.cpp and the README)
#include "colorer.h"
#include "registry.h"

namespace {

// Enumeration datatype Color = C1 | ... | CK; x equals one constructor
class ListDtColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_DT"); }
    void build_variables_and_bounds() override {
        vector<string> names;
        for (int i = 1; i <= K; i++) names.push_back("C" + to_string(i));
        vector<const char*> c_names;
        for (const auto& name : names) c_names.push_back(name.c_str());
        z3::func_decl_vector constructors(ctx), testers(ctx);
        z3::sort color_sort = ctx.enumeration_sort("Color", K, c_names.data(), constructors, testers);
        if (strategies_given()) {
            for (int c = 0; c < K; c++) colors.push_back(constructors[c]());
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), color_sort);
            z3::expr domain = (node_vars[i] == constructors[0]());
            for (int c = 1; c < K; c++) domain = domain || (node_vars[i] == constructors[c]());
            solver.add(domain);
        }
    }
};

// Nat = Z | S(pred: Nat); each node is not K successors deep:
//   not (is-S(x) and is-S(pred x) and ... and is-S(pred^(K-1) x))
class PeanoColorer : public Z3Colorer {
public:
    using Z3Colorer::Z3Colorer;
public:
    bool supports_colors() const override { return true; }
protected:
    void configure_theory() override { set_logic("QF_DT"); }
    void build_variables_and_bounds() override {
        // A recursive datatype goes through the C API: the field "pred" refers to Nat
        // itself (sort reference 0), which the C++ wrapper's constructors::add cannot express
        Z3_symbol pred_name = Z3_mk_string_symbol(ctx, "pred");
        Z3_sort no_sort = nullptr;
        unsigned self = 0;
        Z3_constructor cons[2] = {
            Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "Z"), Z3_mk_string_symbol(ctx, "is-Z"), 0, nullptr, nullptr, nullptr),
            Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "S"), Z3_mk_string_symbol(ctx, "is-S"), 1, &pred_name, &no_sort, &self),
        };
        z3::sort nat_sort(ctx, Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "Nat"), 2, cons));
        ctx.check_error();
        Z3_del_constructor(ctx, cons[0]);
        Z3_del_constructor(ctx, cons[1]);
        z3::func_decl is_s = nat_sort.recognizers()[1];
        z3::func_decl pred = nat_sort.constructors()[1].accessors()[0];
        if (strategies_given()) {
            // the colors Z, S(Z), ..., S^(K-1)(Z)
            z3::expr color = nat_sort.constructors()[0]();
            for (int c = 0; c < K; c++) {
                colors.push_back(color);
                color = nat_sort.constructors()[1](color);
            }
        }

        for (int i = 1; i <= num_nodes; i++) {
            node_vars[i] = constant("node_" + to_string(i), nat_sort);
            vector<z3::expr> deep;
            z3::expr current = node_vars[i];
            for (int j = 0; j < K; j++) {
                deep.push_back(is_s(current));
                current = pred(current);
            }
            solver.add(!all_of(deep));
        }
    }
};

}  // namespace

void register_datatypes(Z3Registry& registry) {
    registry.add("LIST-DT", make<ListDtColorer>());
    registry.add("PEANO", make<PeanoColorer>());
}
