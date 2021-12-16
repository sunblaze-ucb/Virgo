set(CMAKE_CXX_COMPILER mpic++)
set(CMAKE_C_COMPILER mpicc)
cmake_minimum_required(VERSION 3.16)
project(fft_gkr)
include_directories(include .)
include_directories(/usr/lib/x86_64-linux-gnu/openmpi/include/)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -march=native -g")
#we enable optimization by default, you can remove -O3 for debug purpose
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=native -lstdc++ -Wall -march=native -faligned-new -g -DMPI_ENABLED")

add_executable(fft_gkr src/VPD/fft_circuit_GKR.cpp src/linear_gkr/prime_field.cpp src/linear_gkr/polynomial.cpp)
add_executable(zk_proof src/linear_gkr/main.cpp src/infrastructure/utility.cpp src/VPD/fri.cpp src/infrastructure/RS_polynomial.cpp src/infrastructure/merkle_tree.cpp src/VPD/vpd_prover.cpp src/VPD/vpd_verifier.cpp src/linear_gkr/verifier.cpp src/linear_gkr/prime_field.cpp src/linear_gkr/prover.cpp src/linear_gkr/polynomial.cpp src/poly_commitment/poly_commit.cpp)
add_executable(distributed_proof src/distributed_gkr/main.cpp src/linear_gkr/prime_field.cpp src/distributed_gkr/d_verifier.cpp src/distributed_gkr/d_prover.cpp src/infrastructure/utility.cpp src/VPD/fri.cpp src/infrastructure/RS_polynomial.cpp src/infrastructure/merkle_tree.cpp src/VPD/vpd_prover.cpp src/VPD/vpd_verifier.cpp src/linear_gkr/polynomial.cpp src/poly_commitment/poly_commit.cpp)

target_link_libraries(zk_proof -Llib -lflo-shani -lXKCP -lgmp)
target_link_libraries(distributed_proof -Llib -lflo-shani -lXKCP -lgmp)