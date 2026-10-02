cmake_minimum_required(VERSION 3.15)
project(smt_coloring)

# smt-switch requires at least C++11, 17 is standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find the smt-switch libraries in your Linux system
find_library(SMT_SWITCH_LIB NAMES smt-switch HINTS /usr/local/lib REQUIRED)
find_library(SMT_SWITCH_CVC5_LIB NAMES smt-switch-cvc5 HINTS /usr/local/lib REQUIRED)

# Build the UNIFIED Object-Oriented solver
add_executable(smt_solver smt_solver.cpp)
target_link_libraries(smt_solver PRIVATE 
    ${SMT_SWITCH_LIB} 
    ${SMT_SWITCH_CVC5_LIB}
)

find_package(cvc5 REQUIRED)

add_executable(smt_solver_cvc5 smt_solver_cvc5.cpp)
target_include_directories(smt_solver_cvc5 PRIVATE "/root/smt-switch/deps/install/include")
target_link_directories(smt_solver_cvc5 PRIVATE "/root/smt-switch/deps/install/lib")

# Add the poly and cadical libraries right after cvc5 and before gmp!
target_link_libraries(smt_solver_cvc5 PRIVATE cvc5 picpolyxx picpoly cadical gmp)

# FIX: Added 'gmp' to the end of this line!
target_link_libraries(smt_solver_cvc5 PRIVATE cvc5 gmp)