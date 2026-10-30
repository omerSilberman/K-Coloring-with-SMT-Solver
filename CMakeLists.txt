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

# Native cvc5 API version (all theories): every .cpp in cvc5/, one file per theory family.
# CONFIGURE_DEPENDS picks up new files on the next build without re-running cmake by hand.
file(GLOB CVC5_SOURCES CONFIGURE_DEPENDS "${CMAKE_SOURCE_DIR}/cvc5/*.cpp")
add_executable(smt_solver_cvc5 ${CVC5_SOURCES})
target_link_libraries(smt_solver_cvc5 PRIVATE cvc5::cvc5)
# cvc5::cvc5 names cadical, picpoly and picpolyxx without a path; they sit next to libcvc5.
target_link_directories(smt_solver_cvc5 PRIVATE "${cvc5_DIR}/../..")
# Absolute path to the STR-SUB table, so the binary works from any directory
target_compile_definitions(smt_solver_cvc5 PRIVATE
    SUBSTRING_TABLE_PATH="${CMAKE_SOURCE_DIR}/substring_strings.txt")

# Z3 version (the same encodings, where Z3 has the theory): every .cpp in z3/.
# Z3_ROOT is an unpacked Z3 release (https://github.com/Z3Prover/z3/releases, the
# x64-glibc zip): include/z3++.h and bin/libz3.so. Skipped if it is not there.
set(Z3_ROOT "$ENV{HOME}/z3/z3-5.1.0-x64-glibc-2.39" CACHE PATH "Path to an unpacked Z3 release")
if(EXISTS "${Z3_ROOT}/include/z3++.h")
    file(GLOB Z3_SOURCES CONFIGURE_DEPENDS "${CMAKE_SOURCE_DIR}/z3/*.cpp")
    add_executable(smt_solver_z3 ${Z3_SOURCES})
    target_include_directories(smt_solver_z3 SYSTEM PRIVATE "${Z3_ROOT}/include")  # SYSTEM: no warnings from z3++.h
    target_link_libraries(smt_solver_z3 PRIVATE "${Z3_ROOT}/bin/libz3.so")
    # Find libz3.so at run time without LD_LIBRARY_PATH
    set_target_properties(smt_solver_z3 PROPERTIES BUILD_RPATH "${Z3_ROOT}/bin")
    target_compile_definitions(smt_solver_z3 PRIVATE
        SUBSTRING_TABLE_PATH="${CMAKE_SOURCE_DIR}/substring_strings.txt")
else()
    message(STATUS "Z3 not found at ${Z3_ROOT}: smt_solver_z3 is not built (set -DZ3_ROOT=...)")
endif()
