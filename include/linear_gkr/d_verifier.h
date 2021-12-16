#pragma once
#ifndef __d_verifier
#define __d_verifier

#include "linear_gkr/circuit_fast_track.h"
#include "linear_gkr/d_prover.h"
#include "linear_gkr/polynomial.h"
#include <utility>
#include "poly_commitment/poly_commit.h"

extern MPI_Datatype mpiint128_t, mpiu256_t, mpiu512_t, mpifield_element_t, mpilinear_poly_t;

class zk_verifier
{
public:
	poly_commit::poly_commit_verifier poly_ver;
	/** @name Randomness&Const 
	* Storing randomness or constant for simplifying computation/
	*/
	///@{
	prime_field::field_element *beta_g_r0_first_half, *beta_g_r0_second_half;
	prime_field::field_element *beta_g_r1_first_half, *beta_g_r1_second_half;
	prime_field::field_element *beta_u_first_half, *beta_u_second_half;
	prime_field::field_element *beta_v_first_half, *beta_v_second_half;

	prime_field::field_element *beta_g_r0_block_first_half, *beta_g_r0_block_second_half;
	prime_field::field_element *beta_g_r1_block_first_half, *beta_g_r1_block_second_half;
	prime_field::field_element *beta_u_block_first_half, *beta_u_block_second_half;
	prime_field::field_element *beta_v_block_first_half, *beta_v_block_second_half;
	int rank;
	int mpi_world_size;
	///@}
	layered_circuit C; //!< The circuit
	zk_prover *p; //!< The prover
	#ifdef MPI_ENABLED
		void set_rank(int rank, int size);
	#endif
	void beta_init(int depth, prime_field::field_element alpha, prime_field::field_element beta,
	const prime_field::field_element* r_0, const prime_field::field_element* r_1, 
	const prime_field::field_element* r_u, const prime_field::field_element* r_v, 
	const prime_field::field_element* one_minus_r_0, const prime_field::field_element* one_minus_r_1, 
	const prime_field::field_element* one_minus_r_u, const prime_field::field_element* one_minus_r_v);
	void read_circuit(const char *, const char*);
	void read_witness(const char* path_prefix, int rank);
	void read_r1cs(const char *, const char*, const char*, const char*, const char*);
	prime_field::field_element leader_gather_and_continue_sumcheck(linear_poly V_mult_add, linear_poly addV_array, linear_poly add_mult_sum, prime_field::field_element alpha_beta_sum, prime_field::field_element &previous_random, prime_field::field_element* r, int lg_n, int rank, int lg_world, int &proof_size);
	bool verify(const char*);
	void get_prover(zk_prover*);
	void delete_self();
	std::vector<prime_field::field_element> predicates(int depth, prime_field::field_element *r_0, prime_field::field_element *r_1, prime_field::field_element *r_u, prime_field::field_element *r_v, prime_field::field_element alpha, prime_field::field_element beta, int lg_world);
	prime_field::field_element direct_relay(int depth, prime_field::field_element *r_g, prime_field::field_element *r_u, const int lg_world);
	prime_field::field_element V_in(const prime_field::field_element*, const prime_field::field_element*, prime_field::field_element*, int, int);
	prime_field::field_element *VPD_randomness, *one_minus_VPD_randomness;
	void self_inner_product_test(prime_field::field_element alpha_beta_sum, prime_field::field_element v_in);
	/**Test the evaluation of all mask polys after doing random linear combination for them. */
	bool verify_poly_commitment(prime_field::field_element* all_sum, double &v_time, int &proof_size, double &p_time, __hhash_digest merkle_tree_l, __hhash_digest merkle_tree_h);
};

#endif
