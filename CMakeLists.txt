cmake_minimum_required(VERSION 3.15)
project(smt_coloring)

# smt-switch requires at least C++11, 17 is standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find the smt-switch libraries in your Linux system
find_library(SMT_SWITCH_LIB NAMES smt-switch HINTS /usr/local/lib REQUIRED)
find_library(SMT_SWITCH_CVC5_LIB NAMES smt-switch-cvc5 HINTS /usr/local/lib REQUIRED)

# 1. Build the basic solver
add_executable(smt_solver smt_solver.cpp)
target_link_libraries(smt_solver PRIVATE 
    ${SMT_SWITCH_LIB} 
    ${SMT_SWITCH_CVC5_LIB}
)

# 2. Build the symmetry-breaking solver
add_executable(smt_solver_sym smt_solver_sym.cpp)
target_link_libraries(smt_solver_sym PRIVATE 
    ${SMT_SWITCH_LIB} 
    ${SMT_SWITCH_CVC5_LIB}
)

# 3. Build the Bit-Vector solver
add_executable(smt_solver_bv smt_solver_bv.cpp)
target_link_libraries(smt_solver_bv PRIVATE 
    ${SMT_SWITCH_LIB} 
    ${SMT_SWITCH_CVC5_LIB}
)