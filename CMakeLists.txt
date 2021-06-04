cmake_minimum_required(VERSION 3.16)
project(fft_gkr)
include_directories(include)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -march=native -O3")
#we enable optimization by default, you can remove -O3 for debug purpose
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=native -lstdc++ -Wall -march=native -faligned-new -O3")

add_executable(fft_gkr src/VPD/fft_circuit_GKR.cpp src/linear_gkr/prime_field.cpp src/linear_gkr/polynomial.cpp)
add_executable(zk_proof src/linear_gkr/main_zk.cpp src/infrastructure/utility.cpp src/VPD/fri.cpp src/infrastructure/RS_polynomial.cpp src/infrastructure/merkle_tree.cpp src/VPD/vpd_prover.cpp src/VPD/vpd_verifier.cpp src/linear_gkr/zk_verifier.cpp src/linear_gkr/prime_field.cpp src/linear_gkr/zk_prover.cpp src/linear_gkr/polynomial.cpp src/linear_gkr/main_zk.cpp src/poly_commitment/poly_commit.cpp src/infrastructure/fiat_shamir.cpp)

target_link_libraries(zk_proof -Llib -lflo-shani)
