#pragma once
#ifndef __verifier
#define __verifier

#include "linear_gkr/circuit_fast_track.h"
#include "linear_gkr/prover_fast_track.h"
#include "linear_gkr/polynomial.h"
#include <utility>
#include "infrastructure/my_hhash.h"
#include "infrastructure/merkle_tree.h"
#include "infrastructure/RS_polynomial.h"
#include "infrastructure/constants.h"

//low degree test commitment
class ldt_commitment
{
public:
	__hhash_digest* commitment_hhash;
	prime_field::field_element *randomness;
	prime_field::field_element *final_rs_code;
	int mx_depth;
	int repeat_no;
};

//vpd commitment
class vpd_commitment
{
public:
	//do multiple commitment on private data
	__hhash_digest slice_merkle_root[slice_number];

};

class verifier
{
public:

	prime_field::field_element *beta_g_r0_first_half, *beta_g_r0_second_half;
	prime_field::field_element *beta_g_r1_first_half, *beta_g_r1_second_half;
	prime_field::field_element *beta_u_first_half, *beta_u_second_half;
	prime_field::field_element *beta_v_first_half, *beta_v_second_half;

	prime_field::field_element *beta_g_r0_block_first_half, *beta_g_r0_block_second_half;
	prime_field::field_element *beta_g_r1_block_first_half, *beta_g_r1_block_second_half;
	prime_field::field_element *beta_u_block_first_half, *beta_u_block_second_half;
	prime_field::field_element *beta_v_block_first_half, *beta_v_block_second_half;

	prime_field::field_element *beta_g_r0, *beta_g_r1, *beta_u, *beta_v;
	layered_circuit C;
	prover *p;

	//vpd variable
	vpd_commitment vpd_com;
	
	ldt_commitment com[ldt_repeat_num];
	//libra function
	void beta_init(int depth, prime_field::field_element alpha, prime_field::field_element beta,
	const prime_field::field_element* r_0, const prime_field::field_element* r_1, 
	const prime_field::field_element* r_u, const prime_field::field_element* r_v, 
	const prime_field::field_element* one_minus_r_0, const prime_field::field_element* one_minus_r_1, 
	const prime_field::field_element* one_minus_r_u, const prime_field::field_element* one_minus_r_v);
	void read_circuit(const char *, const char *);
	bool verify();
	void get_prover(prover*);
	void delete_self();
	prime_field::field_element mult(int);
	prime_field::field_element add(int);
	prime_field::field_element V_in(const prime_field::field_element*, const prime_field::field_element*, prime_field::field_element*, int, int);
	prime_field::field_element direct_relay(int depth, prime_field::field_element *r_g, prime_field::field_element *r_u);
	prime_field::field_element not_gate(int depth);
	prime_field::field_element minus_gate(int depth);
	prime_field::field_element xor_gate(int depth);
	prime_field::field_element NAAB_gate(int depth);
	prime_field::field_element sum_gate(int depth);
	prime_field::field_element relay_gate(int depth);
	std::vector<prime_field::field_element> predicates(int depth, prime_field::field_element *r_0, prime_field::field_element *r_1, prime_field::field_element *r_u, prime_field::field_element *r_v, prime_field::field_element alpha, prime_field::field_element beta);
	
	//VPD
	__hhash_digest request_init_commit();
	void vpd_init();
	bool verify_merkle(__hhash_digest h, __hhash_digest* merkle, int len, int pow, std::pair<prime_field::field_element, prime_field::field_element> value);
	bool verify_vpd(prime_field::field_element mu, prime_field::field_element* randomness, int len_randomness);
	//Fri proof of proximity
	double v_time;
	ldt_commitment commit_phase(int slice_num);
	bool verify_phase(const ldt_commitment &com, int slice_num, int &delta_merkle_visited);
	std::vector<prime_field::field_element> public_info;
};

#endif
