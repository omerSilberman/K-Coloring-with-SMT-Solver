// smt_solver_cvc5: graph K-coloring with cvc5, in one of many SMT encodings.
//   ./smt_solver_cvc5 <THEORY> <dimacs_file> <K> [--model] [--print-asserts] [--opt NAME=VALUE]...
#include "../common/cli.h"
#include "registry.h"

int main(int argc, char** argv) {
    Cvc5Registry registry(make_element_theory, element_theory_names());
    for (auto register_theory : {register_int, register_bv, register_fp, register_real, register_ff,
                                 register_uf, register_datatypes, register_bool, register_rep,
                                 register_strings, register_sets, register_bags, register_arrays, register_sep}) {
        registry.begin_group();
        register_theory(registry);
    }
    return run_cli(argc, argv, "smt_solver_cvc5", "cvc5", registry);
}
