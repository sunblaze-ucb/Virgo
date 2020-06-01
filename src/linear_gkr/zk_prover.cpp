#include "linear_gkr/zk_prover.h"
#include <iostream>
#include <utility>
#include <vector>
#include "infrastructure/my_hhash.h"
#include "infrastructure/constants.h"
#include "infrastructure/RS_polynomial.h"
#include "infrastructure/utility.h"
#include <queue>
#include <cstring>

prime_field::field_element from_string(const char* str)
{
	prime_field::field_element ret = prime_field::field_element(0);
	int len = strlen(str);
	for(int i = 0; i < len; ++i)
	{
		int digit = str[i] - '0';
		ret = ret * prime_field::field_element(10) + prime_field::field_element(digit);
	}
	return ret;
}
prime_field::field_element inv_2;
void zk_prover::get_circuit(const layered_circuit &from_verifier)
{
	C = from_verifier;
	inv_2 = prime_field::inv(prime_field::field_element(2));
}

prime_field::field_element zk_prover::V_res(const prime_field::field_element* one_minus_r_0, const prime_field::field_element* r_0, const prime_field::field_element* output_raw, int r_0_size, int output_size)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	prime_field::field_element *output;
	output = new prime_field::field_element[output_size];
	for(int i = 0; i < output_size; ++i)
		output[i] = output_raw[i];
	for(int i = 0; i < r_0_size; ++i)
	{
		for(int j = 0; j < (output_size >> 1); ++j)
		{
			output[j] = (output[j << 1] * one_minus_r_0[i] + output[j << 1 | 1] * r_0[i]);
		}
		output_size >>= 1;
	}
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	prime_field::field_element res = output[0];
	delete[] output;
	return res;
}

prime_field::field_element* zk_prover::evaluate()
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	circuit_value[0] = new prime_field::field_element[(1 << C.circuit[0].bit_length)];
	for(int i = 0; i < (1 << C.circuit[0].bit_length); ++i)
	{
		int g, u, ty;
		g = i;
		u = C.circuit[0].gates[g].u;
		ty = C.circuit[0].gates[g].ty;
		assert(ty == 3 || ty == 2);
		circuit_value[0][g] = prime_field::field_element(u);
	}
	assert(C.total_depth < 1000000);
	for(int i = 1; i < C.total_depth; ++i)
	{
		circuit_value[i] = new prime_field::field_element[(1 << C.circuit[i].bit_length)];
		for(int j = 0; j < (1 << C.circuit[i].bit_length); ++j)
		{
			int g, u, v, ty;
			g = j;
			ty = C.circuit[i].gates[g].ty;
			u = C.circuit[i].gates[g].u;
			v = C.circuit[i].gates[g].v;
			if(ty == 0)
			{
				circuit_value[i][g] = circuit_value[i - 1][u] + circuit_value[i - 1][v];
			}
			else if(ty == 1)
			{
				assert(u >= 0 && u < ((1 << C.circuit[i - 1].bit_length)));
				assert(v >= 0 && v < ((1 << C.circuit[i - 1].bit_length)));
				circuit_value[i][g] = circuit_value[i - 1][u] * circuit_value[i - 1][v];
			}
			else if(ty == 2)
			{
				circuit_value[i][g] = prime_field::field_element(0);
			}
			else if(ty == 3)
			{
				circuit_value[i][g] = prime_field::field_element(u);
			}
			else if(ty == 4)
			{
				circuit_value[i][g] = circuit_value[i - 1][u];
			}
			else if(ty == 5)
			{
				circuit_value[i][g] = prime_field::field_element(0);
				for(int k = u; k < v; ++k)
					circuit_value[i][g] = circuit_value[i][g] + circuit_value[i - 1][k];
			}
			else if(ty == 6)
			{
				circuit_value[i][g] = prime_field::field_element(1) - circuit_value[i - 1][u];
			}
			else if(ty == 7)
			{
				circuit_value[i][g] = circuit_value[i - 1][u] - circuit_value[i - 1][v];
			}
			else if(ty == 8)
			{
				auto &x = circuit_value[i - 1][u], &y = circuit_value[i - 1][v];
				circuit_value[i][g] = x + y - prime_field::field_element(2) * x * y;
			}
			else if(ty == 9)
			{
				assert(u >= 0 && u < ((1 << C.circuit[i - 1].bit_length)));
				assert(v >= 0 && v < ((1 << C.circuit[i - 1].bit_length)));
				auto &x = circuit_value[i - 1][u], &y = circuit_value[i - 1][v];
				circuit_value[i][g] = y - x * y;
			}
			else if(ty == 10)
			{
				circuit_value[i][g] = circuit_value[i - 1][u];
			}
			else if(ty == 12)
			{
				circuit_value[i][g] = prime_field::field_element(0);
				assert(v - u + 1 <= 60);
				for(int k = u; k <= v; ++k)
				{
					circuit_value[i][g] = circuit_value[i][g] + circuit_value[i - 1][k] * prime_field::field_element(1ULL << (k - u));
				}
			}
			else if(ty == 13)
			{
				assert(u == v);
				assert(u >= 0 && u < ((1 << C.circuit[i - 1].bit_length)));
				circuit_value[i][g] = circuit_value[i - 1][u] * (prime_field::field_element(1) - circuit_value[i - 1][v]);
			}
			else
			{
				assert(false);
			}
		}
	}

	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	std::cerr << "total evaluation time: " << time_span.count() << " seconds." << std::endl;
	return circuit_value[C.total_depth - 1];
}

//a_0x_0^2 + a_1x_0 + a_2x_1^2 + a_3x_1 + \cdots + a_{2n}


void zk_prover::generate_maskpoly_pre_rho(int length, int degree)
{
	if(maskpoly != NULL) 
		delete[] maskpoly;
	//last 6 for u_n^5, u_n^4, u_n^3 and v_n^5, v_n^4, v_n^3;
	maskpoly = new prime_field::field_element[length * degree + 1 + 6];
	for(int i = 0; i < length * degree + 1 + 6; i++){
		maskpoly[i] = prime_field::random();
		all_pri_mask.push_back(maskpoly[i]);
	}
}

void zk_prover::generate_maskpoly_after_rho(int length, int degree)
{
	for(int i = 0; i < length * degree + 1 + 6; i++){
		maskpoly[i] = maskpoly[i] * rho;
	}
	maskpoly_sumc = maskpoly[length * degree];
	for(int i = length * degree; i >= 0; i--)
		maskpoly_sumc = maskpoly_sumc + maskpoly[i];
	for(int i = 1; i <= 6; i++)
		maskpoly_sumc = maskpoly_sumc + maskpoly[length * degree + i];

	for(int i = 1; i < length; i++)
		maskpoly_sumc = maskpoly_sumc + maskpoly_sumc;
	maskpoly_sumr = prime_field::field_element(0);
}

//new zk function
//a0 + a1g1 + a2g1^2 + a3c + a4c^2 + a5g1c;
void zk_prover::generate_maskR(int layer_id){
//	vpdR::KeyGen(2);
//	std::vector<bn::Ec1> ret;
//	ret.resize(2);

//	std::vector<mpz_class> maskR_gmp;
	//Here we could only use first 6 terms
	for(int i = 0; i < 6; ++i){
//		maskR_gmp.push_back(maskR[i].to_gmp_class());
		all_pri_mask.push_back(maskR[i]);
	}
	prepreu1 = preu1;
	preprev1 = prev1;
//	r_f_R = vpdR::commit(ret[0], ret[1], maskR_gmp);

	//quadratic function of c that R(z, c) when z = g1;

	for(int i = 0; i < 6; i++)
		preR[i] = maskR[i];
	Rg1.a = maskR[4];
	Rg1.b = maskR[3] + maskR[5] * preu1;
	Rg1.c = maskR[0] + maskR[1] * preu1 + maskR[2] * preu1 * preu1; 
	
	//quadratic function of c that R(z, c) when z = g2;

	Rg2.a = maskR[4];
	Rg2.b = maskR[3] + maskR[5] * prev1;
	Rg2.c = maskR[0] + maskR[1] * prev1 + maskR[2] * prev1 * prev1;
	prime_field::field_element sumRu = Rg1.a + Rg1.b + Rg1.c + Rg1.c;
	prime_field::field_element sumRv = Rg2.a + Rg2.b + Rg2.c + Rg2.c;

	maskR_sumcu = alpha * Zu * sumRu;
	maskR_sumcv = beta * Zv * sumRv;

	preZu = Zu;
	preZv = Zv;
	Zu = prime_field::field_element(1);
	Zv = prime_field::field_element(1);
	Iuv = prime_field::field_element(1);
	if(layer_id > 1){
		for(int i = 0; i < 6; i++)
			maskR[i] = prime_field::random();
		sumRc.a = maskR[2] + maskR[2];
		sumRc.b = maskR[1] + maskR[1] + maskR[5];
		sumRc.c = maskR[0] + maskR[0] + maskR[3] + maskR[4];
	} 
	//input randomness
	maskr.resize(2);
	maskr[0] = prime_field::random();
	maskr[1] = prime_field::random();
	if(layer_id == 1){
		//a + bx;
		maskR[0] = maskr[0];
		maskR[1] = maskr[1];
		maskR[2] = 0;
		maskR[3] = 0;
		maskR[4] = 0;
		maskR[5] = 0;
		sumRc.a = prime_field::field_element(0);
		sumRc.b = maskR[1];
		sumRc.c = maskR[0];
	}
//	return ret;
}
/*
std::pair<std::vector<bn::Ec1>, std::vector<bn::Ec1> > zk_prover::prove_R(std::vector<mpz_class> R, mpz_class &ans)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	std::vector<bn::Ec1> witness, witnessa;
	std::vector<mpz_class> input;
	for(int i = 0; i < 6; ++i)
		input.push_back(preR[i].to_gmp_class());
	vpdR::prove(R, ans, input, witness, witnessa, r_f_R);
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	return std::make_pair(witness, witnessa);
}
std::pair<std::vector<bn::Ec1>, std::vector<bn::Ec1> > zk_prover::prove_mask(std::vector<mpz_class> R, mpz_class &ans)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	std::vector<bn::Ec1> witness, witnessa;
	vpd_test::prove(R, ans, maskpoly_gmp, witness, witnessa, r_f_mask_poly);	
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	return std::make_pair(witness, witnessa);
}

*/
prime_field::field_element zk_prover::query(prime_field::field_element *u, prime_field::field_element *v, prime_field::field_element r_c){
	prime_field::field_element result = prime_field::field_element(0);
	for(int i = 0; i < length_u; i++){
		result = result + maskpoly[2*i] * u[i] * u[i] + maskpoly[2*i + 1] * u[i];
		if(i == length_u - 1){
			result = result + maskpoly[2 * (length_u + length_v + 1) + 1] * u[i] * u[i] * u[i] * u[i] * u[i];
			result = result + maskpoly[2 * (length_u + length_v + 1) + 2] * u[i] * u[i] * u[i] * u[i];
			result = result + maskpoly[2 * (length_u + length_v + 1) + 3] * u[i] * u[i] * u[i];
		}
	}
	for(int i = 0; i < length_v; i++){
		result = result + maskpoly[2*(i + length_u)] * v[i] * v[i] + maskpoly[2 * (i + length_u) + 1] * v[i];
		if(i == length_v - 1){
			result = result + maskpoly[2 * (length_u + length_v + 1) + 4] * v[i] * v[i] * v[i] * v[i] * v[i];
			result = result + maskpoly[2 * (length_u + length_v + 1) + 5] * v[i] * v[i] * v[i] * v[i];
			result = result + maskpoly[2 * (length_u + length_v + 1) + 6] * v[i] * v[i] * v[i];
		}
	}
	result = result + maskpoly[2 * (length_u + length_v)] * r_c * r_c + maskpoly[2 * (length_u + length_v) + 1] * r_c;
	result = result + maskpoly[2 * (length_u + length_v + 1)];

	return result;
}	

prime_field::field_element zk_prover::queryRg1(prime_field::field_element r_c){
	return Rg1.eval(r_c);
}

prime_field::field_element zk_prover::queryRg2(prime_field::field_element r_c){
	return Rg2.eval(r_c);	
}

//new zk function
void zk_prover::sumcheck_init(int layer_id, int bit_length_g, int bit_length_u, int bit_length_v, 
	const prime_field::field_element &a, const prime_field::field_element &b, 
	const prime_field::field_element* R_0, const prime_field::field_element* R_1,
	prime_field::field_element* o_r_0, prime_field::field_element *o_r_1)
{
	r_0 = R_0;
	r_1 = R_1;
	alpha = a;
	beta = b;
	sumcheck_layer_id = layer_id;
	length_g = bit_length_g;
	length_u = bit_length_u;
	length_v = bit_length_v;
	one_minus_r_0 = o_r_0;
	one_minus_r_1 = o_r_1;
	generate_maskR(layer_id);
}


bool gate_meet[14];
void zk_prover::init_array(int max_bit_length)
{
	memset(gate_meet, 0, sizeof(bool) * 14);
	add_mult_sum = new linear_poly[(1 << max_bit_length)];
	V_mult_add = new linear_poly[(1 << max_bit_length)];
	addV_array = new linear_poly[(1 << max_bit_length)];
	int half_length = (max_bit_length >> 1) + 1;
	beta_g_r0_fhalf = new prime_field::field_element[(1 << half_length)];
	beta_g_r0_shalf = new prime_field::field_element[(1 << half_length)];
	beta_g_r1_fhalf = new prime_field::field_element[(1 << half_length)];
	beta_g_r1_shalf = new prime_field::field_element[(1 << half_length)];
	beta_u_fhalf = new prime_field::field_element[(1 << half_length)];
	beta_u_shalf = new prime_field::field_element[(1 << half_length)];
}

void zk_prover::delete_self()
{
	delete[] add_mult_sum;
	delete[] V_mult_add;
	delete[] addV_array;

	delete[] beta_g_r0_fhalf;
	delete[] beta_g_r0_shalf;
	delete[] beta_g_r1_fhalf;
	delete[] beta_g_r1_shalf;
	delete[] beta_u_fhalf;
	delete[] beta_u_shalf;
	for(int i = 0; i < C.total_depth; ++i)
		delete[] circuit_value[i];
	delete[] maskpoly;
}

zk_prover::~zk_prover()
{
}



void zk_prover::sumcheck_phase1_init()
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	//mult init
	total_uv = (1 << C.circuit[sumcheck_layer_id - 1].bit_length);
	prime_field::field_element zero = prime_field::field_element(0);
	for(int i = 0; i < total_uv; ++i)
	{
		V_mult_add[i] = circuit_value[sumcheck_layer_id - 1][i];

		addV_array[i].a = zero;
		addV_array[i].b = zero;
		add_mult_sum[i].a = zero;
		add_mult_sum[i].b = zero;
	}
	
	beta_g_r0_fhalf[0] = alpha;
	beta_g_r1_fhalf[0] = beta;
	beta_g_r0_shalf[0] = prime_field::field_element(1);
	beta_g_r1_shalf[0] = prime_field::field_element(1);

	int first_half = length_g >> 1, second_half = length_g - first_half;

	for(int i = 0; i < first_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0_fhalf[j | (1 << i)] = beta_g_r0_fhalf[j] * r_0[i];
			beta_g_r0_fhalf[j] = beta_g_r0_fhalf[j] * one_minus_r_0[i];
			beta_g_r1_fhalf[j | (1 << i)] = beta_g_r1_fhalf[j] * r_1[i];
			beta_g_r1_fhalf[j] = beta_g_r1_fhalf[j] * one_minus_r_1[i];
		}
	}

	for(int i = 0; i < second_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0_shalf[j | (1 << i)] = beta_g_r0_shalf[j] * r_0[i + first_half];
			beta_g_r0_shalf[j] = beta_g_r0_shalf[j] * one_minus_r_0[i + first_half];
			beta_g_r1_shalf[j | (1 << i)] = beta_g_r1_shalf[j] * r_1[i + first_half];
			beta_g_r1_shalf[j] = beta_g_r1_shalf[j] * one_minus_r_1[i + first_half];
		}
	}

	int mask_fhalf = (1 << first_half) - 1;
	
	for(int i = 0; i < (1 << length_g); ++i)
	{
		int u, v;
		u = C.circuit[sumcheck_layer_id].gates[i].u;
		v = C.circuit[sumcheck_layer_id].gates[i].v;
		switch(C.circuit[sumcheck_layer_id].gates[i].ty)
		{
			case 0: //add gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				addV_array[u].b = (addV_array[u].b + circuit_value[sumcheck_layer_id - 1][v] * tmp);
				add_mult_sum[u].b = (add_mult_sum[u].b + tmp);
				break;
			}
			case 2:
			{
				break;
			}
			case 1: //mult gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				add_mult_sum[u].b = (add_mult_sum[u].b + circuit_value[sumcheck_layer_id - 1][v] * tmp);
				break;
			}
			case 5: //sum gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
					+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half];
				for(int j = u; j < v; ++j)
				{
					add_mult_sum[j].b = (add_mult_sum[j].b + tmp);
				}
				break;
			}
			case 12: //exp sum gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
					+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half];
				for(int j = u; j <= v; ++j)
				{
					add_mult_sum[j].b = (add_mult_sum[j].b + tmp);
					tmp = tmp + tmp;
				}
				break;
			}
			case 4: //direct relay gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[u & mask_fhalf] * beta_g_r0_shalf[u >> first_half] 
						+ beta_g_r1_fhalf[u & mask_fhalf] * beta_g_r1_shalf[u >> first_half]);
				add_mult_sum[u].b = (add_mult_sum[u].b + tmp);
				break;
			}
			case 6: //NOT gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				add_mult_sum[u].b = (add_mult_sum[u].b - tmp);
				addV_array[u].b = (addV_array[u].b + tmp);
				break;
			}
			case 7: //minus gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				addV_array[u].b = (addV_array[u].b - (circuit_value[sumcheck_layer_id - 1][v] * tmp));
				add_mult_sum[u].b = (add_mult_sum[u].b + tmp);
				break;
			}
			case 8: //XOR gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				auto tmp_V = tmp * circuit_value[sumcheck_layer_id - 1][v];
				auto tmp_2V = tmp_V + tmp_V;
				addV_array[u].b = (addV_array[u].b + tmp_V);
				add_mult_sum[u].b = (add_mult_sum[u].b + tmp - tmp_2V);
				break;
			}
			case 13: //bit-test gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				auto tmp_V = tmp * circuit_value[sumcheck_layer_id - 1][v];
				add_mult_sum[u].b = (add_mult_sum[u].b - tmp_V + tmp);
				break;
			}
			case 9: //NAAB gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				auto tmpV = tmp * circuit_value[sumcheck_layer_id - 1][v];
				addV_array[u].b = (addV_array[u].b + tmpV);
				add_mult_sum[u].b = (add_mult_sum[u].b - tmpV);
				break;
			}
			case 10: //relay gate
			{
				if(!gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty])
				{
					//printf("first meet %d gate\n", C.circuit[sumcheck_layer_id].gates[i].ty);
					gate_meet[C.circuit[sumcheck_layer_id].gates[i].ty] = true;
				}
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf] * beta_g_r0_shalf[i >> first_half] 
						+ beta_g_r1_fhalf[i & mask_fhalf] * beta_g_r1_shalf[i >> first_half]);
				add_mult_sum[u].b = (add_mult_sum[u].b + tmp);
				break;
			}
			default:
			{
				printf("Warning Unknown gate %d\n", C.circuit[sumcheck_layer_id].gates[i].ty);
				break;
			}
		}
	}
	
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
}


//new zk function
quadratic_poly zk_prover::sumcheck_phase1_update(prime_field::field_element previous_random, int current_bit)
{	
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quadratic_poly ret = quadratic_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	for(int i = 0; i < (total_uv >> 1); ++i)
	{
		prime_field::field_element zero_value, one_value;
		int g_zero = i << 1, g_one = i << 1 | 1;
		if(current_bit == 0)
		{
			V_mult_add[i].b = V_mult_add[g_zero].b;
			V_mult_add[i].a = V_mult_add[g_one].b - V_mult_add[i].b;

			addV_array[i].b = addV_array[g_zero].b;
			addV_array[i].a = addV_array[g_one].b - addV_array[i].b;

			add_mult_sum[i].b = add_mult_sum[g_zero].b;
			add_mult_sum[i].a = add_mult_sum[g_one].b - add_mult_sum[i].b;

		}
		else
		{
			V_mult_add[i].b = (V_mult_add[g_zero].a * previous_random + V_mult_add[g_zero].b);
			V_mult_add[i].a = (V_mult_add[g_one].a * previous_random + V_mult_add[g_one].b - V_mult_add[i].b);

			addV_array[i].b = (addV_array[g_zero].a * previous_random + addV_array[g_zero].b);
			addV_array[i].a = (addV_array[g_one].a * previous_random + addV_array[g_one].b - addV_array[i].b);

			add_mult_sum[i].b = (add_mult_sum[g_zero].a * previous_random + add_mult_sum[g_zero].b);
			add_mult_sum[i].a = (add_mult_sum[g_one].a * previous_random + add_mult_sum[g_one].b - add_mult_sum[i].b);

		}
		ret.a = (ret.a + add_mult_sum[i].a * V_mult_add[i].a);
		ret.b = (ret.b + add_mult_sum[i].a * V_mult_add[i].b + add_mult_sum[i].b * V_mult_add[i].a
									+ addV_array[i].a);
		ret.c = (ret.c + add_mult_sum[i].b * V_mult_add[i].b
									+ addV_array[i].b);
	}

	total_uv >>= 1;
	Iuv = Iuv * (prime_field::field_element(1) - previous_random);
	if(current_bit > 0){
		maskR_sumcu = maskR_sumcu * (prime_field::field_element(1) - previous_random);
		maskR_sumcv = maskR_sumcv * (prime_field::field_element(1) - previous_random);

		Zu = Zu * (prime_field::field_element(1) - previous_random) * previous_random;
	}

	ret.b = ret.b - maskR_sumcu - maskR_sumcv;
	ret.c = ret.c + maskR_sumcu + maskR_sumcv;


	
	//compute with sumcheck maskpol

	prime_field::field_element tmp1, tmp2;
	tmp1 = maskpoly[current_bit << 1];
	tmp2 = maskpoly[(current_bit << 1) + 1];

	for(int i = 0; i < length_u + length_v - current_bit; i++){
		tmp1 = tmp1 + tmp1;
		tmp2 = tmp2 + tmp2;
	}

	maskpoly_sumc = (maskpoly_sumc - tmp1 - tmp2) * inv_2; //take care, inv_2 depends on the field

	prime_field::field_element tmp3;
	if(current_bit > 0){
		maskpoly_sumr = maskpoly_sumr + maskpoly[(current_bit << 1) - 2] * previous_random * previous_random + maskpoly[(current_bit << 1) - 1] * previous_random; 
		tmp3 = maskpoly_sumr;
		for(int i = 0; i < length_u + length_v - current_bit; i++)
			tmp3 = tmp3 + tmp3;
	}

	ret.a = ret.a + tmp1;
	ret.b = ret.b + tmp2;
	ret.c = ret.c + maskpoly_sumc + tmp3;
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	return ret;
}

quintuple_poly zk_prover::sumcheck_phase1_updatelastbit(prime_field::field_element previous_random, int current_bit)
{	
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quintuple_poly ret = quintuple_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	for(int i = 0; i < (total_uv >> 1); ++i)
	{
		prime_field::field_element zero_value, one_value;
		int g_zero = i << 1, g_one = i << 1 | 1;
		if(current_bit == 0)
		{
			V_mult_add[i].b = V_mult_add[g_zero].b;
			V_mult_add[i].a = V_mult_add[g_one].b - V_mult_add[i].b;

			addV_array[i].b = addV_array[g_zero].b;
			addV_array[i].a = addV_array[g_one].b - addV_array[i].b;

			add_mult_sum[i].b = add_mult_sum[g_zero].b;
			add_mult_sum[i].a = add_mult_sum[g_one].b - add_mult_sum[i].b;

		}
		else
		{
			V_mult_add[i].b = (V_mult_add[g_zero].a * previous_random + V_mult_add[g_zero].b);
			V_mult_add[i].a = (V_mult_add[g_one].a * previous_random + V_mult_add[g_one].b - V_mult_add[i].b);

			addV_array[i].b = (addV_array[g_zero].a * previous_random + addV_array[g_zero].b);
			addV_array[i].a = (addV_array[g_one].a * previous_random + addV_array[g_one].b - addV_array[i].b);

			add_mult_sum[i].b = (add_mult_sum[g_zero].a * previous_random + add_mult_sum[g_zero].b);
			add_mult_sum[i].a = (add_mult_sum[g_one].a * previous_random + add_mult_sum[g_one].b - add_mult_sum[i].b);

		}
		ret.a = (ret.a + add_mult_sum[i].a * V_mult_add[i].a);
		ret.b = (ret.b + add_mult_sum[i].a * V_mult_add[i].b + add_mult_sum[i].b * V_mult_add[i].a
									+ addV_array[i].a);
		ret.c = (ret.c + add_mult_sum[i].b * V_mult_add[i].b
									+ addV_array[i].b);
	}

	total_uv >>= 1;

	//compute with maskpolyR
	
	Iuv = Iuv * (prime_field::field_element(1) - previous_random);

	if(current_bit > 0){
		maskR_sumcv = maskR_sumcv * (prime_field::field_element(1) - previous_random);
		maskR_sumcu = maskR_sumcu * (prime_field::field_element(1) - previous_random);
		Zu = Zu * (prime_field::field_element(1) - previous_random) * previous_random;
	}

	ret.b = ret.b - maskR_sumcu - maskR_sumcv;
	ret.c = ret.c + maskR_sumcu + maskR_sumcv;
	
	//compute with sumcheck maskpol
	
	if(current_bit == length_u - 1){
		prime_field::field_element a = sumRc.a;
		prime_field::field_element b = sumRc.b;
		prime_field::field_element c = sumRc.c;
		prime_field::field_element d = add_mult_sum[0].a;
		prime_field::field_element e = add_mult_sum[0].b;
		ret.d = (prime_field::field_element(0) - a) * d * Zu;
		ret.e = (a * (d - e) - b * d) * Zu;
		ret.f = (a * e + b * (d - e) - c * d) * Zu;
		ret.a = ret.a + (c * (d - e) + b * e) * Zu;  
		ret.b = ret.b + c * e * Zu;
	}
	
	prime_field::field_element tmp1, tmp2, tmp4, tmp5, tmp6;
	tmp1 = maskpoly[current_bit << 1];
	tmp2 = maskpoly[(current_bit << 1) + 1];
	tmp4 = maskpoly[((length_u + length_v + 1) << 1) + 1];
	tmp5 = maskpoly[((length_u + length_v + 1) << 1) + 2];
	tmp6 = maskpoly[((length_u + length_v + 1) << 1) + 3];

	for(int i = 0; i < length_u + length_v - current_bit; i++){
		tmp1 = tmp1 + tmp1;
		tmp2 = tmp2 + tmp2;
		tmp4 = tmp4 + tmp4;
		tmp5 = tmp5 + tmp5;
		tmp6 = tmp6 + tmp6;
	}

	maskpoly_sumc = (maskpoly_sumc - tmp1 - tmp2 - tmp4 - tmp5 - tmp6) * inv_2;

	prime_field::field_element tmp3;
	if(current_bit > 0){
		maskpoly_sumr = maskpoly_sumr + maskpoly[(current_bit << 1) - 2] * previous_random * previous_random + maskpoly[(current_bit << 1) - 1] * previous_random; 
		tmp3 = maskpoly_sumr;
		for(int i = 0; i < length_u + length_v - current_bit; i++)
			tmp3 = tmp3 + tmp3;
	}

	ret.a = (ret.a + tmp1);
	ret.b = (ret.b + tmp2);
	ret.c = (ret.c + maskpoly_sumc + tmp3);
	ret.d = ret.d + tmp4;
	ret.e = ret.e + tmp5;
	ret.f = ret.f + tmp6;

	quintuple_poly ret5(ret.d, ret.e, ret.f, ret.a, ret.b, ret.c);
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	return ret5;
}

void zk_prover::sumcheck_phase2_init(prime_field::field_element previous_random, const prime_field::field_element* r_u, const prime_field::field_element* one_minus_r_u)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	preu1 = previous_random;
	maskR_sumcu = maskR_sumcu * (prime_field::field_element(1) - previous_random);
	maskR_sumcv = maskR_sumcv * (prime_field::field_element(1) - previous_random);

	Iuv = Iuv * (prime_field::field_element(1) - previous_random);
	v_u = V_mult_add[0].eval(previous_random);
	
	Zu = Zu * (prime_field::field_element(1) - previous_random) * previous_random; 
	v_u = v_u + Zu * sumRc.eval(previous_random);

	int first_half = length_u >> 1, second_half = length_u - first_half;

	beta_u_fhalf[0] = prime_field::field_element(1);
	beta_u_shalf[0] = prime_field::field_element(1);
	for(int i = 0; i < first_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u_fhalf[j | (1 << i)] = beta_u_fhalf[j] * r_u[i];
			beta_u_fhalf[j] = beta_u_fhalf[j] * one_minus_r_u[i];
		}
	}

	for(int i = 0; i < second_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u_shalf[j | (1 << i)] = beta_u_shalf[j] * r_u[i + first_half];
			beta_u_shalf[j] = beta_u_shalf[j] * one_minus_r_u[i + first_half];
		}
	}

	int mask_fhalf = (1 << first_half) - 1;
	int first_g_half = (length_g >> 1);
	int mask_g_fhalf = (1 << (length_g >> 1)) - 1;
	
	total_uv = (1 << C.circuit[sumcheck_layer_id - 1].bit_length);
	int total_g = (1 << C.circuit[sumcheck_layer_id].bit_length);
	prime_field::field_element zero = prime_field::field_element(0);
	for(int i = 0; i < total_uv; ++i)
	{
		add_mult_sum[i].a = zero;
		add_mult_sum[i].b = zero;
		addV_array[i].a = zero;
		addV_array[i].b = zero;
		V_mult_add[i] = circuit_value[sumcheck_layer_id - 1][i];
	}

	for(int u = 0; u < total_uv; ++u)
	{

	}
	
	for(int i = 0; i < total_g; ++i)
	{
		int ty = C.circuit[sumcheck_layer_id].gates[i].ty;
		int u = C.circuit[sumcheck_layer_id].gates[i].u;
		int v = C.circuit[sumcheck_layer_id].gates[i].v;
		switch(ty)
		{
			case 1: //mult gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				add_mult_sum[v].b = add_mult_sum[v].b + (tmp_g * tmp_u * v_u);
				add_mult_sum[v].b = add_mult_sum[v].b;
				break;
			}
			case 0: //add gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp_g_u = tmp_g * tmp_u;
				add_mult_sum[v].b = (add_mult_sum[v].b + tmp_g_u);
				addV_array[v].b = (tmp_g_u * v_u + addV_array[v].b);

				addV_array[v].b = addV_array[v].b;
				break;
			}
			case 2:
			{
				break;
			}
			case 4:
			{
				break;
			}
			case 5: //sum gate
			{
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp_g_vu = tmp_g * v_u;
				for(int j = u; j < v; ++j)
				{
					auto tmp_u = beta_u_fhalf[j & mask_fhalf] * beta_u_shalf[j >> first_half];
					addV_array[0].b = (addV_array[0].b + tmp_g_vu * tmp_u);
				}
				break;
			}
			case 12: //exp sum gate
			{
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp_g_vu = tmp_g * v_u;
				
				for(int j = u; j <= v; ++j)
				{
					auto tmp_u = beta_u_fhalf[j & mask_fhalf] * beta_u_shalf[j >> first_half];
					addV_array[0].b = (addV_array[0].b + tmp_g_vu * tmp_u);
					tmp_g_vu = tmp_g_vu + tmp_g_vu;
				}
				break;
			}
			case 6: //not gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp_g_u = tmp_g * tmp_u;
				addV_array[v].b = (addV_array[v].b + tmp_g_u - tmp_g_u * v_u);
				break;
			}
			case 7: //minus gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp = tmp_g * tmp_u;
				add_mult_sum[v].b = (add_mult_sum[v].b - tmp);
				addV_array[v].b = (tmp * v_u + addV_array[v].b);
				break;
			}
			case 8: //xor gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp = tmp_g * tmp_u;
				auto tmp_v_u = tmp * v_u;
				add_mult_sum[v].b = (add_mult_sum[v].b + tmp - tmp_v_u - tmp_v_u);
				addV_array[v].b = (addV_array[v].b + tmp_v_u);
				break;
			}
			case 13: //bit-test gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp = tmp_g * tmp_u;
				auto tmp_v_u = tmp * v_u;
				add_mult_sum[v].b = (add_mult_sum[v].b - tmp_v_u);
				addV_array[v].b = (addV_array[v].b + tmp_v_u);
				break;
			}
			case 9: //NAAB gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp = tmp_g * tmp_u;
				add_mult_sum[v].b = (add_mult_sum[v].b + tmp - v_u * tmp);
				break;
			}
			case 10: //relay gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf] * beta_u_shalf[u >> first_half];
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf] * beta_g_r0_shalf[i >> first_g_half] 
								+ beta_g_r1_fhalf[i & mask_g_fhalf] * beta_g_r1_shalf[i >> first_g_half]);
				auto tmp = tmp_g * tmp_u;
				addV_array[v].b = (addV_array[v].b + tmp * v_u);
				break;
			}
			default:
			{
				printf("Warning Unknown gate %d\n", ty);
				break;
			}
		}
	}

	//update maskpoly
	maskpoly_sumr = maskpoly_sumr + maskpoly[length_u * 2 - 2] * previous_random * previous_random + maskpoly[length_u * 2 - 1] * previous_random;
	maskpoly_sumr = maskpoly_sumr + maskpoly[(length_u + length_v + 1) * 2 + 1] * previous_random * previous_random * previous_random * previous_random * previous_random;
	maskpoly_sumr = maskpoly_sumr + maskpoly[(length_u + length_v + 1) * 2 + 2] * previous_random * previous_random * previous_random * previous_random;
	maskpoly_sumr = maskpoly_sumr + maskpoly[(length_u + length_v + 1) * 2 + 3] * previous_random * previous_random * previous_random;
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
}


//new zk function

quadratic_poly zk_prover::sumcheck_phase2_update(prime_field::field_element previous_random, int current_bit)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quadratic_poly ret = quadratic_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	for(int i = 0; i < (total_uv >> 1); ++i)
	{
		int g_zero = i << 1, g_one = i << 1 | 1;
		if(current_bit == 0)
		{
			V_mult_add[i].b = V_mult_add[g_zero].b;
			V_mult_add[i].a = V_mult_add[g_one].b - V_mult_add[i].b;

			addV_array[i].b = addV_array[g_zero].b;
			addV_array[i].a = addV_array[g_one].b - addV_array[i].b;

			add_mult_sum[i].b = add_mult_sum[g_zero].b;
			add_mult_sum[i].a = add_mult_sum[g_one].b - add_mult_sum[i].b;
		}
		else
		{
			
			V_mult_add[i].b = (V_mult_add[g_zero].a * previous_random + V_mult_add[g_zero].b);
			V_mult_add[i].a = (V_mult_add[g_one].a * previous_random + V_mult_add[g_one].b - V_mult_add[i].b);

			addV_array[i].b = (addV_array[g_zero].a * previous_random + addV_array[g_zero].b);
			addV_array[i].a = (addV_array[g_one].a * previous_random + addV_array[g_one].b - addV_array[i].b);

			add_mult_sum[i].b = (add_mult_sum[g_zero].a * previous_random + add_mult_sum[g_zero].b);
			add_mult_sum[i].a = (add_mult_sum[g_one].a * previous_random + add_mult_sum[g_one].b - add_mult_sum[i].b);
		}

		ret.a = (ret.a + add_mult_sum[i].a * V_mult_add[i].a);
		ret.b = (ret.b + add_mult_sum[i].a * V_mult_add[i].b
									+	add_mult_sum[i].b * V_mult_add[i].a
									+ addV_array[i].a);
		ret.c = (ret.c + add_mult_sum[i].b * V_mult_add[i].b
									+ addV_array[i].b);
	}

	total_uv >>= 1;
	//maskR
	if(current_bit > 0) 
		Iuv = Iuv * (prime_field::field_element(1) - previous_random);

	if(current_bit > 0){
		maskR_sumcu = maskR_sumcu * (prime_field::field_element(1) - previous_random);
		maskR_sumcv = maskR_sumcv * (prime_field::field_element(1) - previous_random);
		Zv = Zv * (prime_field::field_element(1) - previous_random) * previous_random;
	}
	ret.b = ret.b - maskR_sumcu - maskR_sumcv;
	ret.c = ret.c + maskR_sumcu + maskR_sumcv;


	//mask sumcheck
	int current = current_bit + length_u;

	prime_field::field_element tmp1, tmp2;
	tmp1 = maskpoly[current << 1];
	tmp2 = maskpoly[(current << 1) + 1];
	for(int i = 0; i < length_u + length_v - current; i++){
		tmp1 = tmp1 + tmp1;
		tmp2 = tmp2 + tmp2;
	}
	maskpoly_sumc = (maskpoly_sumc - tmp1 - tmp2) * inv_2;

	prime_field::field_element tmp3;
	maskpoly_sumr = maskpoly_sumr + maskpoly[(current << 1) - 2] * previous_random * previous_random + maskpoly[(current << 1) - 1] * previous_random; 
	
	tmp3 = maskpoly_sumr;
	for(int i = 0; i < length_u + length_v - current; i++)
		tmp3 = tmp3 + tmp3;
	

	ret.a = (ret.a + tmp1);
	ret.b = (ret.b + tmp2);
	ret.c = (ret.c + maskpoly_sumc + tmp3);
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	return ret;
}

quintuple_poly zk_prover::sumcheck_phase2_updatelastbit(prime_field::field_element previous_random, int current_bit)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quintuple_poly ret = quintuple_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	for(int i = 0; i < (total_uv >> 1); ++i)
	{
		int g_zero = i << 1, g_one = i << 1 | 1;
		if(current_bit == 0)
		{
			V_mult_add[i].b = V_mult_add[g_zero].b;
			V_mult_add[i].a = V_mult_add[g_one].b - V_mult_add[i].b;

			addV_array[i].b = addV_array[g_zero].b;
			addV_array[i].a = addV_array[g_one].b - addV_array[i].b;

			add_mult_sum[i].b = add_mult_sum[g_zero].b;
			add_mult_sum[i].a = add_mult_sum[g_one].b - add_mult_sum[i].b;
		}
		else
		{
			
			V_mult_add[i].b = (V_mult_add[g_zero].a * previous_random + V_mult_add[g_zero].b);
			V_mult_add[i].a = (V_mult_add[g_one].a * previous_random + V_mult_add[g_one].b - V_mult_add[i].b);

			addV_array[i].b = (addV_array[g_zero].a * previous_random + addV_array[g_zero].b);
			addV_array[i].a = (addV_array[g_one].a * previous_random + addV_array[g_one].b - addV_array[i].b);

			add_mult_sum[i].b = (add_mult_sum[g_zero].a * previous_random + add_mult_sum[g_zero].b);
			add_mult_sum[i].a = (add_mult_sum[g_one].a * previous_random + add_mult_sum[g_one].b - add_mult_sum[i].b);
		}

		ret.a = (ret.a + add_mult_sum[i].a * V_mult_add[i].a);
		ret.b = (ret.b + add_mult_sum[i].a * V_mult_add[i].b
									+	add_mult_sum[i].b * V_mult_add[i].a
									+ addV_array[i].a);
		ret.c = (ret.c + add_mult_sum[i].b * V_mult_add[i].b
									+ addV_array[i].b);
	}

	total_uv >>= 1;
	//maskR
	Iuv = Iuv * (prime_field::field_element(1) - previous_random);

	if(current_bit > 0){
		maskR_sumcu = maskR_sumcu * (prime_field::field_element(1) - previous_random);

		maskR_sumcv = maskR_sumcv * (prime_field::field_element(1) - previous_random);
		Zv = Zv * (prime_field::field_element(1) - previous_random) * previous_random;
	}
	ret.b = ret.b - maskR_sumcu - maskR_sumcv;
	ret.c = ret.c + maskR_sumcu + maskR_sumcv;
	if(current_bit == length_v - 1){
		prime_field::field_element a = sumRc.a;
		prime_field::field_element b = sumRc.b;
		prime_field::field_element c = sumRc.c;
		prime_field::field_element d = add_mult_sum[0].a;
		prime_field::field_element e = add_mult_sum[0].b;
		ret.d = (prime_field::field_element(0) - a) * d * Zv;
		ret.e = (a * (d - e) - b * d) * Zv;
		ret.f = (a * e + b * (d - e) - c * d) * Zv;
		ret.a = ret.a + (c * (d - e) + b * e) * Zv;  
		ret.b = ret.b + c * e * Zv;
	}
	//mask sumcheck
	int current = current_bit + length_u;

	prime_field::field_element tmp1, tmp2, tmp4, tmp5, tmp6;
	tmp1 = maskpoly[current << 1];
	tmp2 = maskpoly[(current << 1) + 1];
	tmp4 = maskpoly[(length_u + length_v + 1) * 2 + 4];
	tmp5 = maskpoly[(length_u + length_v + 1) * 2 + 5];
	tmp6 = maskpoly[(length_u + length_v + 1) * 2 + 6];

	for(int i = 0; i < length_u + length_v - current; i++){
		tmp1 = tmp1 + tmp1;
		tmp2 = tmp2 + tmp2;
		tmp4 = tmp4 + tmp4;
		tmp5 = tmp5 + tmp5;
		tmp6 = tmp6 + tmp6;
	}
	maskpoly_sumc = (maskpoly_sumc - tmp1 - tmp2 - tmp4 - tmp5 - tmp6) * inv_2;

	prime_field::field_element tmp3;
	maskpoly_sumr = maskpoly_sumr + maskpoly[(current << 1) - 2] * previous_random * previous_random + maskpoly[(current << 1) - 1] * previous_random; 
	tmp3 = maskpoly_sumr;
	for(int i = 0; i < length_u + length_v - current; i++)
		tmp3 = tmp3 + tmp3;
	
	ret.d = ret.d + tmp4;
	ret.e = ret.e + tmp5;
	ret.f = ret.f + tmp6;

	ret.a = (ret.a + tmp1);
	ret.b = (ret.b + tmp2);
	ret.c = (ret.c + maskpoly_sumc + tmp3);
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	quintuple_poly ret5(ret.d, ret.e, ret.f, ret.a, ret.b, ret.c);
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	return ret5;
}

quadratic_poly zk_prover::sumcheck_finalround(prime_field::field_element previous_random, int current, prime_field::field_element general_value){
	quadratic_poly ret = quadratic_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	//to do
	ret.a = Iuv * preZu * Rg1.a * alpha + Iuv * preZv * Rg2.a * beta;
	ret.b = Iuv * preZu * Rg1.b * alpha + Iuv * preZv * Rg2.b * beta + general_value;
	ret.c = Iuv * preZu * Rg1.c * alpha + Iuv * preZv * Rg2.c * beta;
	
	prime_field::field_element tmp1, tmp2;
	tmp1 = maskpoly[current << 1];
	tmp2 = maskpoly[(current << 1) + 1];
	for(int i = 0; i < length_u + length_v - current; i++){
		tmp1 = tmp1 + tmp1;
		tmp2 = tmp2 + tmp2;
	}
	maskpoly_sumc = (maskpoly_sumc - tmp1 - tmp2) * inv_2;

	prime_field::field_element tmp3;
	maskpoly_sumr = maskpoly_sumr + maskpoly[(current << 1) - 2] * previous_random * previous_random + maskpoly[(current << 1) - 1] * previous_random; 
	maskpoly_sumr = maskpoly_sumr + maskpoly[(length_u + length_v + 1) * 2 + 4] * previous_random * previous_random * previous_random * previous_random * previous_random; 
	maskpoly_sumr = maskpoly_sumr + maskpoly[(length_u + length_v + 1) * 2 + 5] * previous_random * previous_random * previous_random * previous_random; 
	maskpoly_sumr = maskpoly_sumr + maskpoly[(length_u + length_v + 1) * 2 + 6] * previous_random * previous_random * previous_random; 

	tmp3 = maskpoly_sumr;
	for(int i = 0; i < length_u + length_v - current; i++)
		tmp3 = tmp3 + tmp3;
	
	ret.a = (ret.a + tmp1);
	ret.b = (ret.b + tmp2);
	ret.c = (ret.c + maskpoly_sumc + tmp3);
	return ret;
};


std::pair<prime_field::field_element, prime_field::field_element> zk_prover::sumcheck_finalize(prime_field::field_element previous_random)
{
	prev1 = previous_random;
	Iuv = Iuv * (prime_field::field_element(1) - previous_random);
	v_v = V_mult_add[0].eval(previous_random);
	Zv = Zv * (prime_field::field_element(1) - previous_random) * previous_random;
	
	v_v = v_v + Zv * sumRc.eval(previous_random);
	return std::make_pair(v_u, v_v);
}
void zk_prover::proof_init()
{
	//todo
}
prime_field::field_element *all_pri_msk_arr;
prime_field::field_element *all_pub_msk_arr;
prime_field::field_element *inner_prod_evals;
prime_field::field_element *l_coef, *l_eval, *q_coef, *q_eval; //l for private input, q for public randomness
prime_field::field_element *q_eval_real; //the real input part
prime_field::field_element *lq_eval, *h_coef, *lq_coef, *h_eval;
prime_field::field_element *h_eval_arr;
int l_coef_len, l_eval_len, q_coef_len, q_eval_len;
int slice_size, slice_count, slice_real_ele_cnt;
int mask_position_gap; //masks are positioned in specific way for efficiency
bool pre_prepare_executed = false;
__hhash_digest zk_prover::prover_vpd_prepare()
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	pre_prepare_executed = true;
	slice_count = 1 << log_slice_number;
	slice_count ++; //for masks
	slice_size = (1 << (C.circuit[0].bit_length + rs_code_rate - log_slice_number));
	slice_real_ele_cnt = slice_size >> rs_code_rate;
	//prepare polynomial division/decomposition
	//things are going to be sliced
	//get evaluations
	l_eval_len = slice_count * slice_size;
	l_eval = new prime_field::field_element[l_eval_len];
	mask_position_gap = slice_size / all_pri_mask.size();
	for(int j = 0; j < 64; ++j)
	{
		if((1LL << j) <= mask_position_gap && (1LL << (j + 1)) > mask_position_gap)
		{
			mask_position_gap = 1LL << j;
			break;
		}
	}
	//padding masks
	int mask_size_after_padding = slice_size / mask_position_gap;

	while(all_pri_mask.size() < mask_size_after_padding)
		all_pri_mask.push_back(prime_field::field_element(0));

	prime_field::field_element *tmp;
	tmp = new prime_field::field_element[max(mask_size_after_padding, slice_real_ele_cnt)];

	auto fft_t0 = std::chrono::high_resolution_clock::now();

	init_scratch_pad(slice_size);
	for(int i = 0; i < slice_count; ++i)
	{
		if(i == slice_count - 1)
		{
			all_pri_msk_arr = new prime_field::field_element[mask_size_after_padding];
			for(int j = 0; j < mask_size_after_padding; ++j)
				all_pri_msk_arr[j] = all_pri_mask[j];
			inverse_fast_fourier_transform(all_pri_msk_arr, mask_size_after_padding, mask_size_after_padding, prime_field::get_root_of_unity(mylog(mask_size_after_padding)), tmp);
			fast_fourier_transform(tmp, mask_size_after_padding, slice_size, prime_field::get_root_of_unity(mylog(slice_size)), &l_eval[(i * slice_size)]);
		}
		else
		{
			bool all_zero = true;
			auto zero = prime_field::field_element(0);
			for(int j = 0; j < slice_real_ele_cnt; ++j)
			{
				if(circuit_value[0][i * slice_real_ele_cnt + j] == zero)
					continue;
				all_zero = false;
				break;
			}
			if(all_zero)
			{
				for(int j = 0; j < slice_size; ++j)
					l_eval[i * slice_size + j] = zero;
			}
			else
			{
				inverse_fast_fourier_transform(&circuit_value[0][i * slice_real_ele_cnt], slice_real_ele_cnt, slice_real_ele_cnt, prime_field::get_root_of_unity(mylog(slice_real_ele_cnt)), tmp);
				fast_fourier_transform(tmp, slice_real_ele_cnt, slice_size, prime_field::get_root_of_unity(mylog(slice_size)), &l_eval[i * slice_size]);
			}
		}
	}

	auto fft_t1 = std::chrono::high_resolution_clock::now();
	//printf("FFT Prepare time %lf\n", std::chrono::duration_cast<std::chrono::duration<double>>(fft_t1 - fft_t0).count());
	delete[] tmp;
	
	auto ret = vpd_prover_init(l_eval, l_coef, C.circuit[0].bit_length, slice_size, slice_count);
	
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	//printf("VPD prepare time %lf\n", time_span.count());
	return ret;
}

void dfs_for_public_eval(int dep, prime_field::field_element val, prime_field::field_element *r_0, prime_field::field_element *one_minus_r_0, int r_0_len, int pos)
{
	if(dep == r_0_len)
		q_eval_real[pos] = val;
	else
	{
		dfs_for_public_eval(dep + 1, val * one_minus_r_0[r_0_len - 1 - dep], r_0, one_minus_r_0, r_0_len, pos << 1);
		dfs_for_public_eval(dep + 1, val * r_0[r_0_len - 1 - dep], r_0, one_minus_r_0, r_0_len, pos << 1 | 1);
	}
}


__hhash_digest zk_prover::prover_vpd_prepare_post_gkr(std::vector<prime_field::field_element> &all_pub_msk, prime_field::field_element *r_0, prime_field::field_element *one_minus_r_0, int r_0_len, prime_field::field_element target_sum, prime_field::field_element *all_sum)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	assert(pre_prepare_executed);
	fri::virtual_oracle_witness = new prime_field::field_element[slice_size * slice_count];
	fri::virtual_oracle_witness_msk = new prime_field::field_element[slice_size];
	fri::virtual_oracle_witness_msk_mapping = new int[slice_size];
	fri::virtual_oracle_witness_mapping = new int[slice_size * slice_count];
	q_eval_len = l_eval_len;
	q_eval_real = new prime_field::field_element[1 << C.circuit[0].bit_length];
	q_eval = new prime_field::field_element[q_eval_len];
	dfs_for_public_eval(0, prime_field::field_element(1), r_0, one_minus_r_0, r_0_len, 0);
	int mask_size_after_padding = slice_size / mask_position_gap;
	assert(mask_size_after_padding >= all_pri_mask.size());
	while(all_pub_msk.size() < mask_size_after_padding)
		all_pub_msk.push_back(prime_field::field_element(0));
	all_pub_msk_arr = new prime_field::field_element[all_pub_msk.size()];
	for(int i = 0; i < all_pub_msk.size(); ++i)
		all_pub_msk_arr[i] = all_pub_msk[i];
	prime_field::field_element *tmp;
	tmp = new prime_field::field_element[max(all_pub_msk.size(), slice_size)];
	prime_field::field_element *all_pub_msk_eval = new prime_field::field_element[slice_size];
	
	double fft_time = 0;
	double re_mapping_time = 0;
	
	auto fft_t0 = std::chrono::high_resolution_clock::now();

	inverse_fast_fourier_transform(all_pub_msk_arr, all_pub_msk.size(), all_pub_msk.size(), prime_field::get_root_of_unity(mylog(all_pub_msk.size())), tmp);
	fast_fourier_transform(tmp, all_pub_msk.size(), slice_size, prime_field::get_root_of_unity(mylog(slice_size)), all_pub_msk_eval);


	for(int i = 0; i < all_pub_msk.size(); ++i)
	{
		assert(all_pub_msk[i] == all_pub_msk_eval[i * mask_position_gap]);
	}
	for(int i = 0; i < slice_count; ++i)
	{
		if(i == slice_count - 1)
		{
			for(int j = 0; j < slice_size; ++j)
			{
				q_eval[j + (i * slice_size)] = all_pub_msk_eval[j];
			}
		}
		else
		{
			inverse_fast_fourier_transform(&q_eval_real[i * slice_real_ele_cnt], slice_real_ele_cnt, slice_real_ele_cnt, prime_field::get_root_of_unity(mylog(slice_real_ele_cnt)), tmp);
			fast_fourier_transform(tmp, slice_real_ele_cnt, slice_size, prime_field::get_root_of_unity(mylog(slice_size)), &q_eval[i * slice_size]);
		}
	}
	
	auto fft_t1 = std::chrono::high_resolution_clock::now();
	fft_time += std::chrono::duration_cast<std::chrono::duration<double>>(fft_t1 - fft_t0).count();

	prime_field::field_element sum = prime_field::field_element(0);
	assert((slice_count - 1) * slice_real_ele_cnt == (1 << C.circuit[0].bit_length));
	for(int i = 0; i < (slice_count - 1) * slice_real_ele_cnt; ++i)
	{
		assert((i << rs_code_rate) < q_eval_len);
		sum = sum + q_eval[i << rs_code_rate] * l_eval[i << rs_code_rate];
	}
	assert(mylog(slice_size / all_pub_msk.size()) == mylog(mask_position_gap));
	for(int i = 0; i < slice_size; i += mask_position_gap)
	{
		sum = sum + all_pri_mask[i / mask_position_gap] * all_pub_msk[i / mask_position_gap];
		assert(all_pub_msk[i / mask_position_gap] == q_eval[i + (slice_count - 1) * slice_size]);
		assert(all_pri_mask[i / mask_position_gap] == l_eval[i + (slice_count - 1) * slice_size]);
	}
	assert(sum == target_sum);
	//do fft for q_eval
	//experiment
	//poly mul first
	lq_eval = new prime_field::field_element[max(2 * slice_size / mask_position_gap, 2 * slice_real_ele_cnt)];
	h_coef = new prime_field::field_element[max(slice_real_ele_cnt, slice_size / mask_position_gap)];
	lq_coef = new prime_field::field_element[max(2 * slice_size / mask_position_gap, 2 * slice_real_ele_cnt)];
	h_eval = new prime_field::field_element[max(slice_size, max(slice_size / mask_position_gap, slice_real_ele_cnt))];
	h_eval_arr = new prime_field::field_element[slice_count * slice_size];
	const int log_leaf_size = log_slice_number + 1;
	for(int i = 0; i < slice_count; ++i)
	{
		if(i == slice_count - 1)
		{
			assert(mask_position_gap != 1);
			int id = 0;
			bool all_zero = true;
			auto zero = prime_field::field_element(0);
			for(int j = 0; j < slice_size; j += mask_position_gap / 2, id++)
			{
				lq_eval[id] = l_eval[i * slice_size + j] * q_eval[i * slice_size + j];
				if(!(lq_eval[id] == zero))
				{
					all_zero = false;
				}
			}
			if(all_zero)
			{
				for(int j = 0; j < 2 * slice_size / mask_position_gap; ++j)
					lq_coef[j] = zero;
				for(int j = 0; j < slice_size / mask_position_gap; ++j)
					h_coef[j] = zero;
				for(int j = 0; j < slice_size; ++j)
					h_eval[j] = zero;
			}
			else
			{
				fft_t0 = std::chrono::high_resolution_clock::now();
				inverse_fast_fourier_transform(lq_eval, 2 * slice_size / mask_position_gap, 2 * slice_size / mask_position_gap, prime_field::get_root_of_unity(mylog(2 * slice_size / mask_position_gap)), lq_coef);
				for(int j = 0; j < slice_size / mask_position_gap; ++j)
				{
					h_coef[j] = lq_coef[j + slice_size / mask_position_gap];
				}
				fast_fourier_transform(h_coef, slice_size / mask_position_gap, slice_size, prime_field::get_root_of_unity(mylog(slice_size)), h_eval);
				fft_t1 = std::chrono::high_resolution_clock::now();
				fft_time += std::chrono::duration_cast<std::chrono::duration<double>>(fft_t1 - fft_t0).count();
			}
			//test
			auto rou = prime_field::get_root_of_unity(mylog(slice_size));
			auto inv_x = prime_field::field_element(1);
			auto rou_n = prime_field::fast_pow(rou, slice_size / mask_position_gap);
			auto x_n = prime_field::field_element(1);
			auto inv_rou = prime_field::inv(rou);
			for(int j = 0; j < slice_size; ++j)
			{
			//	assert(l_eval[i * slice_size + j] * q_eval[i * slice_size + j] == g_eval[i][j] + (prime_field::fast_pow(x, slice_size / mask_position_gap) - 1) * h_eval[i][j]);
				auto g = l_eval[i * slice_size + j] * q_eval[i * slice_size + j] - (x_n - 1) * h_eval[j];
				if(j < slice_size / 2)
				{
					fri::virtual_oracle_witness_msk[j << 1] = (g - (lq_coef[0] + h_coef[0])) * prime_field::field_element(slice_size / mask_position_gap) * inv_x;
					fri::virtual_oracle_witness_msk_mapping[j] = j << 1;
				}
				else
				{
					int jj = j - slice_size / 2;
					fri::virtual_oracle_witness_msk[jj << 1 | 1] = (g - (lq_coef[0] + h_coef[0])) * prime_field::field_element(slice_size / mask_position_gap) * inv_x;
					fri::virtual_oracle_witness_msk_mapping[j] = jj << 1;
				}
				inv_x = inv_x * inv_rou;
				x_n = x_n * rou_n;
			}
			all_sum[i] = (lq_coef[0] + h_coef[0]) * prime_field::field_element(slice_size / mask_position_gap);
		}
		else
		{
			assert(2 * slice_real_ele_cnt <= slice_size);
			bool all_zero = true;
			auto zero = prime_field::field_element(0);
			for(int j = 0; j < 2 * slice_real_ele_cnt; ++j)
			{
				lq_eval[j] = l_eval[i * slice_size + j * (slice_size / (2 * slice_real_ele_cnt))] * q_eval[i * slice_size + j * (slice_size / (2 * slice_real_ele_cnt))];
				if(lq_eval[j] != zero)
				{
					all_zero = false;
				}
			}
			if(all_zero)
			{
				for(int j = 0; j < 2 * slice_real_ele_cnt; ++j)
					lq_coef[j] = zero;
				for(int j = 0; j < slice_real_ele_cnt; ++j)
					h_coef[j] = zero;
				for(int j = 0; j < slice_size; ++j)
					h_eval[j] = zero;
			}
			else
			{
				fft_t0 = std::chrono::high_resolution_clock::now();
				inverse_fast_fourier_transform(lq_eval, 2 * slice_real_ele_cnt, 2 * slice_real_ele_cnt, prime_field::get_root_of_unity(mylog(2 * slice_real_ele_cnt)), lq_coef);
				for(int j = 0; j < slice_real_ele_cnt; ++j)
					h_coef[j] = lq_coef[j + slice_real_ele_cnt];
				fast_fourier_transform(h_coef, slice_real_ele_cnt, slice_size, prime_field::get_root_of_unity(mylog(slice_size)), h_eval);
				fft_t1 = std::chrono::high_resolution_clock::now();
				fft_time += std::chrono::duration_cast<std::chrono::duration<double>>(fft_t1 - fft_t0).count();
			}
			auto rou = prime_field::get_root_of_unity(mylog(slice_size));
			auto inv_rou = prime_field::inv(rou);
			auto rou_n = prime_field::fast_pow(rou, slice_real_ele_cnt);
			auto x_n = prime_field::field_element(1);
			auto inv_x = prime_field::field_element(slice_real_ele_cnt); //absorb the constant factor
			auto remap_t0 = std::chrono::high_resolution_clock::now();
			auto const_sum = prime_field::field_element(0) - (lq_coef[0] + h_coef[0]);
			for(int j = 0; j < slice_size; ++j)
			{
			//	assert(l_eval[i * slice_size + j] * q_eval[i * slice_size + j] == g_eval[i][j] + (prime_field::fast_pow(x, slice_real_ele_cnt) - 1) * h_eval[i][j]);
				auto g = l_eval[i * slice_size + j] * q_eval[i * slice_size + j] - (x_n - 1) * h_eval[j];
				if(j < slice_size / 2)
				{
					fri::virtual_oracle_witness[(j) << log_leaf_size | (i << 1) | 0] = (g + const_sum) * inv_x;
					fri::virtual_oracle_witness_mapping[j << log_slice_number | i] = j << log_leaf_size | (i << 1) | 0;
				}
				else
				{
					int jj = j - slice_size / 2;
					fri::virtual_oracle_witness[(jj) << log_leaf_size | (i << 1) | 1] = (g + const_sum) * inv_x;
					fri::virtual_oracle_witness_mapping[jj << log_slice_number | i] = jj << log_leaf_size | (i << 1) | 0;
				}
				inv_x = inv_x * inv_rou;
				x_n = x_n * rou_n;
			}
			auto remap_t1 = std::chrono::high_resolution_clock::now();
			re_mapping_time += std::chrono::duration_cast<std::chrono::duration<double>>(remap_t1 - remap_t0).count();
			assert(i < slice_number + 1);
			all_sum[i] = (lq_coef[0] + h_coef[0]) * prime_field::field_element(slice_real_ele_cnt);
		}
		for(int j = 0; j < slice_size; ++j)
			h_eval_arr[i * slice_size + j] = h_eval[j];
	}
	delete[] tmp;
	delete[] lq_eval;
	delete[] h_coef;
	delete[] lq_coef;
	delete[] h_eval;
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	//printf("PostGKR FFT time %lf\n", fft_time);
	//printf("PostGKR remap time %lf\n", re_mapping_time);
	//printf("PostGKR prepare time 0 %lf\n", time_span.count());
	
	t0 = std::chrono::high_resolution_clock::now();
	auto ret = fri::request_init_commit(C.circuit[0].bit_length, 1);
	t1 = std::chrono::high_resolution_clock::now();
	time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	
	//printf("PostGKR prepare time 1 %lf\n", time_span.count());
	return ret;
}