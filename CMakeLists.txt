cmake_minimum_required(VERSION 3.15)
project(smt_test)

# smt-switch requires at least C++11, 17 is standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(smt_test main.cpp)

# Find the smt-switch libraries in your Linux system
find_library(SMT_SWITCH_LIB NAMES smt-switch HINTS /usr/local/lib REQUIRED)
find_library(SMT_SWITCH_CVC5_LIB NAMES smt-switch-cvc5 HINTS /usr/local/lib REQUIRED)

# Link them to your test executable
target_link_libraries(smt_test PRIVATE 
    ${SMT_SWITCH_LIB} 
    ${SMT_SWITCH_CVC5_LIB}
)

add_executable(smt_solver_sym smt_solver_sym.cpp)
target_link_libraries(smt_solver_sym PRIVATE ${SMT_SWITCH_LIB} ${SMT_SWITCH_CVC5_LIB})