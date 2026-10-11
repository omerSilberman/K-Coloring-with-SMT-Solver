cmake_minimum_required(VERSION 3.15)
project(smt_coloring CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# smt-switch checkout built with `./configure.sh --cvc5 --prefix=<checkout>/install`.
# install/ holds smt-switch itself, deps/cvc5 holds the cvc5 it built.
set(SMT_SWITCH_DIR "$ENV{HOME}/smt-switch" CACHE PATH "Path to the smt-switch checkout")
list(APPEND CMAKE_PREFIX_PATH "${SMT_SWITCH_DIR}/install" "${SMT_SWITCH_DIR}/deps/cvc5")

# Also finds cvc5 (and GMP, CaDiCaL, libpoly) through smt-switch's package config.
find_package(SmtSwitch REQUIRED COMPONENTS cvc5)

# smt-switch version (subset of the theories)
add_executable(smt_solver smt_solver.cpp)
target_link_libraries(smt_solver PRIVATE SmtSwitch::smt-switch-cvc5)

# Native cvc5 API version (all theories)
add_executable(smt_solver_cvc5 smt_solver_cvc5.cpp)
target_link_libraries(smt_solver_cvc5 PRIVATE cvc5::cvc5)
# cvc5::cvc5 names cadical, picpoly and picpolyxx without a path; they sit next to libcvc5.
target_link_directories(smt_solver_cvc5 PRIVATE "${cvc5_DIR}/../..")
# Absolute path to the STR-SUB table, so the binary works from any directory
target_compile_definitions(smt_solver_cvc5 PRIVATE
    SUBSTRING_TABLE_PATH="${CMAKE_SOURCE_DIR}/substring_strings.txt")
