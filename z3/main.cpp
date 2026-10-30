// smt_solver_z3: graph K-coloring with Z3, in the same encodings as smt_solver_cvc5
// (those Z3 supports).
//   ./smt_solver_z3 <THEORY> <dimacs_file> <K> [--model] [--print-asserts] [--opt NAME=VALUE]...
#include "../common/cli.h"
#include "registry.h"

int main(int argc, char** argv) {
    Z3Registry registry(make_element_theory, element_theory_names());
    for (auto register_theory : {register_int, register_bv, register_fp, register_real, register_uf,
                                 register_datatypes, register_bool, register_strings, register_sets,
                                 register_arrays}) {
        registry.begin_group();
        register_theory(registry);
    }
    return run_cli(argc, argv, "smt_solver_z3", "Z3", registry);
}
