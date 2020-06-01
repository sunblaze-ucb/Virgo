#include "linear_gkr/verifier_fast_track.h"
#include <string>
#include <utility>
#include <iostream>
#include "linear_gkr/random_generator.h"
#include <vector>
#include <iostream>

using namespace std;

void verifier::get_prover(prover *pp)
{
	p = pp;
}

void verifier::read_circuit(const char *path, const char *meta_path)
{
	int d;
	int constraint_count = 0;
	int gate_counter = 0;
	FILE *circuit_in;
	FILE *meta_in;

	meta_in = fopen(meta_path, "r");
	circuit_in = fopen(path, "r");

	fscanf(circuit_in, "%d", &d);
	int n;
	C.circuit = new layer[d + 1];
	C.total_depth = d + 1;
	int max_bit_length = -1;
	for(int i = 1; i <= d; ++i)
	{
		fscanf(circuit_in, "%d", &n);
		gate_counter += n;
		if(i != 1)
		{
			if(n == 1)
				C.circuit[i].gates = new gate[2];
			else
				C.circuit[i].gates = new gate[n];
		}
		else
		{
			if(n == 1)
			{
				C.circuit[0].gates = new gate[2];
				C.circuit[1].gates = new gate[2];
			}
			else
			{
				C.circuit[0].gates = new gate[n];
				C.circuit[1].gates = new gate[n];
			}
		}
		
		int max_gate = -1;
		int previous_g = -1;
		for(int j = 0; j < n; ++j)
		{
			int ty, g;
			long long u, v;
			fscanf(circuit_in, "%d%d%lld%lld", &ty, &g, &u, &v);
			if(ty == 1 || ty == 8 || ty == 9)
			{
				constraint_count++;
			}
			if(ty != 3)
			{
				if(ty == 5)
				{
					assert(u >= 0 && u < (1 << C.circuit[i - 1].bit_length));
					assert(v > u && v <= (1 << C.circuit[i - 1].bit_length));
				}
				else
				{
					if(!(u >= 0 && u < (1 << C.circuit[i - 1].bit_length)))
						cout << ty << " " << g << " " << u << " " << v << " " << (1 << C.circuit[i - 1].bit_length) << endl;
					assert(u >= 0 && u < (1 << C.circuit[i - 1].bit_length));
					if(!(v >= 0 && v < (1 << C.circuit[i - 1].bit_length)))
						cout << ty << " " << g << " " << u << " " << v << " " << (1 << C.circuit[i - 1].bit_length) << endl;
					assert(v >= 0 && v < (1 << C.circuit[i - 1].bit_length));
				}
			}
			if(ty == 6)
			{
				if(v != 0)
					fprintf(stderr, "WARNING, v!=0 for NOT gate.\n");
				v = 0;
			}
			if(ty == 10)
			{
				if(v != 0)
					fprintf(stderr, "WARNING, v!=0 for relay gate. %d\n", i);
				v = 0;
			}
			if(g != previous_g + 1)
			{
				printf("Error, gates must be in sorted order, and full [0, 2^n - 1]. %d %d %d %d\n", i, j, g, previous_g);
				exit(0);
			}
			previous_g = g;
			if(i != 1)
				C.circuit[i].gates[g] = gate(ty, u, v);
			else
			{
				assert(ty == 2 || ty == 3);
				C.circuit[1].gates[g] = gate(4, g, 0);
				C.circuit[0].gates[g] = gate(ty, u, v);
			}
		}
		max_gate = previous_g;
		int cnt = 0;
		while(max_gate)
		{
			cnt++;
			max_gate >>= 1;
		}
		max_gate = 1;
		while(cnt)
		{
			max_gate <<= 1;
			cnt--;
		}
		int mx_gate = max_gate;
		while(mx_gate)
		{
			cnt++;
			mx_gate >>= 1;
		}
		if(n == 1)
		{
			//add a dummy gate to avoid ill-defined layer.
			if(i != 1)
			{
				C.circuit[i].gates[max_gate] = gate(2, 0, 0);
				C.circuit[i].bit_length = cnt;
			}
			else
			{
				C.circuit[0].gates[max_gate] = gate(2, 0, 0);
				C.circuit[0].bit_length = cnt;
				C.circuit[1].gates[max_gate] = gate(4, 1, 0);
				C.circuit[1].bit_length = cnt;
			}
		}
		else
		{
			C.circuit[i].bit_length = cnt - 1;
			if(i == 1)
				C.circuit[0].bit_length = cnt - 1;
		}
		fprintf(stderr, "layer %d, bit_length %d\n", i, C.circuit[i].bit_length);
		if(C.circuit[i].bit_length > max_bit_length)
			max_bit_length = C.circuit[i].bit_length;
	}
	C.circuit[0].is_parallel = false;
	for(int i = 1; i <= d; ++i)
	{
		int is_para;
		fscanf(meta_in, "%d", &is_para);
		fscanf(meta_in, "%d%d%d%d", &C.circuit[i].block_size, &C.circuit[i].repeat_num, &C.circuit[i].log_block_size, &C.circuit[i].log_repeat_num);
		assert(1 << C.circuit[i].log_repeat_num == C.circuit[i].repeat_num);
		if(is_para)
		{
			C.circuit[i].is_parallel = true;
		}
		else
		{
			C.circuit[i].is_parallel = false;
		}
		
	}
	
	int proof_size_byte = 0;
	for(int i = C.total_depth - 1; i >= 0; --i)
	{
		//3 means verifier sends randomness(1) and prover sends a quad poly(3)
		//quad poly + 2 *  四次多项式 + mask + oracle(v_u v_v)
		proof_size_byte += sizeof(prime_field::field_element) * ((C.circuit[i].bit_length - 1) * 3 * 2 + 2 * 6 + 2 + 2);
	}
	std::cerr << "Proof size(byte): " << proof_size_byte << std::endl;
	p -> init_array(max_bit_length);

	int first_half_len = max_bit_length / 2, second_half_len = max_bit_length - first_half_len;
	beta_g_r0_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_g_r0_second_half = new prime_field::field_element[(1 << second_half_len)];
	beta_g_r1_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_g_r1_second_half = new prime_field::field_element[(1 << second_half_len)];
	beta_v_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_v_second_half = new prime_field::field_element[(1 << second_half_len)];
	beta_u_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_u_second_half = new prime_field::field_element[(1 << second_half_len)];

	beta_g_r0_block_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_g_r0_block_second_half = new prime_field::field_element[(1 << second_half_len)];
	beta_g_r1_block_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_g_r1_block_second_half = new prime_field::field_element[(1 << second_half_len)];
	beta_v_block_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_v_block_second_half = new prime_field::field_element[(1 << second_half_len)];
	beta_u_block_first_half = new prime_field::field_element[(1 << first_half_len)];
	beta_u_block_second_half = new prime_field::field_element[(1 << second_half_len)];
	printf("Constaint counter: %d\n", constraint_count);
	printf("Gate number: %d\n", gate_counter);
	fclose(circuit_in);
	fclose(meta_in);
}

prime_field::field_element verifier::add(int depth)
{
	//brute force for sanity check
	//it's slow
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 0)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}
prime_field::field_element verifier::mult(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 1)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::not_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 6)
		{
			assert(v == 0);
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::xor_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 8)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::minus_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 7)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::NAAB_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 9)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::sum_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 5)
		{
			for(int j = u; j < v; ++j)
				ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * (beta_v[0]) * (beta_u[j]);
		}
	}
	return ret;
}
/*

void verifier::beta_init(int depth, prime_field::field_element alpha, prime_field::field_element beta,
	const prime_field::field_element* r_0, const prime_field::field_element* r_1, 
	const prime_field::field_element* r_u, const prime_field::field_element* r_v, 
	const prime_field::field_element* one_minus_r_0, const prime_field::field_element* one_minus_r_1, 
	const prime_field::field_element* one_minus_r_u, const prime_field::field_element* one_minus_r_v)
{
	beta_g_r0[0] = alpha;
	beta_g_r1[0] = beta;
	for(int i = 0; i < C.circuit[depth].bit_length; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0[j | (1 << i)] = beta_g_r0[j] * r_0[i];
			beta_g_r1[j | (1 << i)] = beta_g_r1[j] * r_1[i];
		}
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0[j] = beta_g_r0[j] * one_minus_r_0[i];
			beta_g_r1[j] = beta_g_r1[j] * one_minus_r_1[i];
		}
	}
	beta_u[0] = prime_field::field_element(1);
	beta_v[0] = prime_field::field_element(1);
	for(int i = 0; i < C.circuit[depth - 1].bit_length; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u[j | (1 << i)] = beta_u[j] * r_u[i];
			beta_v[j | (1 << i)] = beta_v[j] * r_v[i];
		}
			
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u[j] = beta_u[j] * one_minus_r_u[i];
			beta_v[j] = beta_v[j] * one_minus_r_v[i];
		}
	}
}
 */
prime_field::field_element verifier::direct_relay(int depth, prime_field::field_element *r_g, prime_field::field_element *r_u)
{
	if(depth != 1)
		return prime_field::field_element(0);
	else
	{
		prime_field::field_element ret = prime_field::field_element(1);
		for(int i = 0; i < C.circuit[depth].bit_length; ++i)
			ret = ret * (prime_field::field_element(1) - r_g[i] - r_u[i] + prime_field::field_element(2) * r_g[i] * r_u[i]);
		return ret;
	}
}

prime_field::field_element* generate_randomness(unsigned int size)
{
	int k = size;
	prime_field::field_element* ret;
	ret = new prime_field::field_element[k];

	for(int i = 0; i < k; ++i)
	{
		ret[i] = prime_field::random();
	}
	return ret;
}

prime_field::field_element verifier::V_in(const prime_field::field_element* r_0, const prime_field::field_element* one_minus_r_0,
								prime_field::field_element* output_raw, int r_0_size, int output_size)
{
	prime_field::field_element* output = new prime_field::field_element[output_size];
	for(int i = 0; i < output_size; ++i)
		output[i] = output_raw[i];
	for(int i = 0; i < r_0_size; ++i)
	{
		for(int j = 0; j < (output_size >> 1); ++j)
			output[j] = output[j << 1] * (one_minus_r_0[i]) + output[j << 1 | 1] * (r_0[i]);
		output_size >>= 1;
	}
	auto ret = output[0];
	delete[] output;
	return ret;
}

prime_field::field_element verifier::relay_gate(const int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 10)
		{
			assert(v == 0);
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * (beta_u[u]) * (beta_v[v]);
		}
	}
	return ret;
}


void verifier::beta_init(int depth, prime_field::field_element alpha, prime_field::field_element beta,
	const prime_field::field_element* r_0, const prime_field::field_element* r_1, 
	const prime_field::field_element* r_u, const prime_field::field_element* r_v, 
	const prime_field::field_element* one_minus_r_0, const prime_field::field_element* one_minus_r_1, 
	const prime_field::field_element* one_minus_r_u, const prime_field::field_element* one_minus_r_v)
{
	bool debug_mode = false;
	if(!C.circuit[depth].is_parallel || debug_mode)
	{
		beta_g_r0_first_half[0] = alpha;
		beta_g_r1_first_half[0] = beta;
		beta_g_r0_second_half[0] = prime_field::field_element(1);
		beta_g_r1_second_half[0] = prime_field::field_element(1);
		int first_half_len = C.circuit[depth].bit_length / 2;
		int second_half_len = C.circuit[depth].bit_length - first_half_len;
		for(int i = 0; i < first_half_len; ++i)
		{
			auto r0 = r_0[i], r1 = r_1[i];
			auto or0 = one_minus_r_0[i], or1 = one_minus_r_1[i];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_first_half[j | (1 << i)] = beta_g_r0_first_half[j] * r0;
				beta_g_r1_first_half[j | (1 << i)] = beta_g_r1_first_half[j] * r1;
			}
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_first_half[j] = beta_g_r0_first_half[j] * or0;
				beta_g_r1_first_half[j] = beta_g_r1_first_half[j] * or1;
			}
		}
		for(int i = 0; i < second_half_len; ++i)
		{
			auto r0 = r_0[i + first_half_len], r1 = r_1[i + first_half_len];
			auto or0 = one_minus_r_0[i + first_half_len], or1 = one_minus_r_1[i + first_half_len];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_second_half[j | (1 << i)] = beta_g_r0_second_half[j] * r0;
				beta_g_r1_second_half[j | (1 << i)] = beta_g_r1_second_half[j] * r1;
			}
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_second_half[j] = beta_g_r0_second_half[j] * or0;
				beta_g_r1_second_half[j] = beta_g_r1_second_half[j] * or1;
			}
		}

		beta_u_first_half[0] = prime_field::field_element(1);
		beta_v_first_half[0] = prime_field::field_element(1);
		beta_u_second_half[0] = prime_field::field_element(1);
		beta_v_second_half[0] = prime_field::field_element(1);
		first_half_len = C.circuit[depth - 1].bit_length / 2;
		second_half_len = C.circuit[depth - 1].bit_length - first_half_len;

		for(int i = 0; i < first_half_len; ++i)
		{
			auto ru = r_u[i], rv = r_v[i];
			auto oru = one_minus_r_u[i], orv = one_minus_r_v[i];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_first_half[j | (1 << i)] = beta_u_first_half[j] * ru;
				beta_v_first_half[j | (1 << i)] = beta_v_first_half[j] * rv;
			}
				
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_first_half[j] = beta_u_first_half[j] * oru;
				beta_v_first_half[j] = beta_v_first_half[j] * orv;
			}
		}

		for(int i = 0; i < second_half_len; ++i)
		{
			auto ru = r_u[i + first_half_len], rv = r_v[i + first_half_len];
			auto oru = one_minus_r_u[i + first_half_len], orv = one_minus_r_v[i + first_half_len];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_second_half[j | (1 << i)] = beta_u_second_half[j] * ru;
				beta_v_second_half[j | (1 << i)] = beta_v_second_half[j] * rv;
			}
				
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_second_half[j] = beta_u_second_half[j] * oru;
				beta_v_second_half[j] = beta_v_second_half[j] * orv;
			}
		}
	}
	if(C.circuit[depth].is_parallel)
	{
		beta_g_r0_block_first_half[0] = alpha;
		beta_g_r1_block_first_half[0] = beta;
		beta_g_r0_block_second_half[0] = prime_field::field_element(1);
		beta_g_r1_block_second_half[0] = prime_field::field_element(1);
		int first_half_len = C.circuit[depth].log_block_size / 2;
		int second_half_len = C.circuit[depth].log_block_size - first_half_len;
		for(int i = 0; i < first_half_len; ++i)
		{
			auto r0 = r_0[i], r1 = r_1[i];
			auto or0 = one_minus_r_0[i], or1 = one_minus_r_1[i];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_block_first_half[j | (1 << i)] = beta_g_r0_block_first_half[j] * r0;
				beta_g_r1_block_first_half[j | (1 << i)] = beta_g_r1_block_first_half[j] * r1;
			}
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_block_first_half[j] = beta_g_r0_block_first_half[j] * or0;
				beta_g_r1_block_first_half[j] = beta_g_r1_block_first_half[j] * or1;
			}
		}
		for(int i = 0; i < second_half_len; ++i)
		{
			auto r0 = r_0[i + first_half_len], r1 = r_1[i + first_half_len];
			auto or0 = one_minus_r_0[i + first_half_len], or1 = one_minus_r_1[i + first_half_len];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_block_second_half[j | (1 << i)] = beta_g_r0_block_second_half[j] * r0;
				beta_g_r1_block_second_half[j | (1 << i)] = beta_g_r1_block_second_half[j] * r1;
			}
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_g_r0_block_second_half[j] = beta_g_r0_block_second_half[j] * or0;
				beta_g_r1_block_second_half[j] = beta_g_r1_block_second_half[j] * or1;
			}
		}

		beta_u_block_first_half[0] = prime_field::field_element(1);
		beta_v_block_first_half[0] = prime_field::field_element(1);
		beta_u_block_second_half[0] = prime_field::field_element(1);
		beta_v_block_second_half[0] = prime_field::field_element(1);
		first_half_len = C.circuit[depth - 1].log_block_size / 2;
		second_half_len = C.circuit[depth - 1].log_block_size - first_half_len;

		for(int i = 0; i < first_half_len; ++i)
		{
			auto ru = r_u[i], rv = r_v[i];
			auto oru = one_minus_r_u[i], orv = one_minus_r_v[i];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_block_first_half[j | (1 << i)] = beta_u_block_first_half[j] * ru;
				beta_v_block_first_half[j | (1 << i)] = beta_v_block_first_half[j] * rv;
			}
				
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_block_first_half[j] = beta_u_block_first_half[j] * oru;
				beta_v_block_first_half[j] = beta_v_block_first_half[j] * orv;
			}
		}

		for(int i = 0; i < second_half_len; ++i)
		{
			auto ru = r_u[i + first_half_len], rv = r_v[i + first_half_len];
			auto oru = one_minus_r_u[i + first_half_len], orv = one_minus_r_v[i + first_half_len];
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_block_second_half[j | (1 << i)] = beta_u_block_second_half[j] * ru;
				beta_v_block_second_half[j | (1 << i)] = beta_v_block_second_half[j] * rv;
			}
				
			for(int j = 0; j < (1 << i); ++j)
			{
				beta_u_block_second_half[j] = beta_u_block_second_half[j] * oru;
				beta_v_block_second_half[j] = beta_v_block_second_half[j] * orv;
			}
		}
	}
}

std::vector<prime_field::field_element> verifier::predicates(int depth, prime_field::field_element *r_0, prime_field::field_element *r_1, prime_field::field_element *r_u, prime_field::field_element *r_v, prime_field::field_element alpha, prime_field::field_element beta)
{
	std::vector<prime_field::field_element> ret_para;
	std::vector<prime_field::field_element> ret;
	ret.resize(11);
	ret_para.resize(11);
	for(int i = 0; i < 11; ++i)
	{
		ret[i] = prime_field::field_element(0);
		ret_para[i] = prime_field::field_element(0);
	}
	if(depth == 1)
	{
		return ret;
	}
	bool debug_mode = false;
	if(C.circuit[depth].is_parallel)
	{
		int first_half_g = C.circuit[depth].log_block_size / 2;
		int second_half_g = C.circuit[depth].log_block_size - first_half_g;
		int first_half_uv = C.circuit[depth - 1].log_block_size / 2;
		int second_half_uv = C.circuit[depth - 1].log_block_size - first_half_uv;
		int block_size = C.circuit[depth].block_size;
		std::vector<prime_field::field_element> one_block_alpha, one_block_beta;
		one_block_alpha.resize(11);
		one_block_beta.resize(11);
		for(int i = 0; i < 11; ++i)
		{
			one_block_alpha[i] = prime_field::field_element(0);
			one_block_beta[i] = prime_field::field_element(0);
		}
		assert((1 << C.circuit[depth].log_block_size) == C.circuit[depth].block_size);
		for(int i = 0; i < (1 << C.circuit[depth].log_block_size); ++i)
		{
			int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
			g = g & ((1 << C.circuit[depth].log_block_size) - 1);
			u = u & ((1 << C.circuit[depth - 1].log_block_size) - 1);
			v = v & ((1 << C.circuit[depth - 1].log_block_size) - 1);
			switch(C.circuit[depth].gates[i].ty)
			{
				case 0:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[0] = one_block_alpha[0] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[0] = one_block_beta[0] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
				case 1:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[1] = one_block_alpha[1] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[1] = one_block_beta[1] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
				case 2:
				{
					break;
				}
				case 3:
				{
					break;
				}
				case 4:
				{
					break;
				}
				case 5:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					
					auto beta_g_val_alpha = beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half];
					auto beta_g_val_beta = beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half];
					auto beta_v_0 = beta_v_block_first_half[0] * beta_v_block_second_half[0];
					for(int j = u; j < v; ++j)
					{
						int u_first_half = j & ((1 << first_half_uv) - 1);
						int u_second_half = j >> first_half_uv;
						one_block_alpha[5] = one_block_alpha[5] + beta_g_val_alpha * beta_v_0 * (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half]);
						one_block_beta[5] = one_block_beta[5] + beta_g_val_beta * beta_v_0 * (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half]);
					}
					break;
				}
				case 6:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[6] = one_block_alpha[6] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[6] = one_block_beta[6] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
				case 7:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[7] = one_block_alpha[7] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[7] = one_block_beta[7] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
				case 8:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[8] = one_block_alpha[8] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[8] = one_block_beta[8] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
				case 9:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[9] = one_block_alpha[9] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[9] = one_block_beta[9] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
				case 10:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half] ) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half] ) ;
					one_block_alpha[10] = one_block_alpha[10] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half])  * uv_value;
					one_block_beta[10] = one_block_beta[10] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half])  * uv_value;
					break;
				}
			}
		}
		auto one = prime_field::field_element(1);
		for(int i = 0; i < C.circuit[depth].repeat_num; ++i)
		{
			prime_field::field_element prefix_alpha, prefix_beta;
			prime_field::field_element prefix_alpha_v0, prefix_beta_v0;
			prefix_alpha = one;
			prefix_beta = one;
			prefix_alpha_v0 = one;
			prefix_beta_v0 = one;
			for(int j = 0; j < C.circuit[depth].log_repeat_num; ++j)
			{
				if((i >> j) & 1)
				{
					auto uv_value = r_u[j + C.circuit[depth - 1].log_block_size] * r_v[j + C.circuit[depth - 1].log_block_size];
					prefix_alpha = prefix_alpha * r_0[j + C.circuit[depth].log_block_size] * uv_value;
					prefix_beta = prefix_beta * r_1[j + C.circuit[depth].log_block_size] * uv_value;
				}
				else
				{
					auto uv_value = (one - r_u[j + C.circuit[depth - 1].log_block_size]) * (one - r_v[j + C.circuit[depth - 1].log_block_size]);
					prefix_alpha = prefix_alpha * (one - r_0[j + C.circuit[depth].log_block_size]) * uv_value;
					prefix_beta = prefix_beta * (one - r_1[j + C.circuit[depth].log_block_size]) * uv_value;
				}
			}
			for(int j = 0; j < C.circuit[depth].log_repeat_num; ++j)
			{
				if((i >> j) & 1)
				{
					auto uv_value = r_u[j + C.circuit[depth - 1].log_block_size] * (one - r_v[j + C.circuit[depth - 1].log_block_size]);
					prefix_alpha_v0 = prefix_alpha_v0 * r_0[j + C.circuit[depth].log_block_size] * uv_value;
					prefix_beta_v0 = prefix_beta_v0 * r_1[j + C.circuit[depth].log_block_size] * uv_value;
				}
				else
				{
					auto uv_value = (one - r_u[j + C.circuit[depth - 1].log_block_size]) * (one - r_v[j + C.circuit[depth - 1].log_block_size]);
					prefix_alpha_v0 = prefix_alpha_v0 * (one - r_0[j + C.circuit[depth].log_block_size]) * uv_value;
					prefix_beta_v0 = prefix_beta_v0 * (one - r_1[j + C.circuit[depth].log_block_size]) * uv_value;
				}
			}
			for(int j = 0; j < 11; ++j)
			{
				if(j == 6 || j == 10 || j == 5)
				{
					ret_para[j] = ret_para[j] + prefix_alpha_v0 * one_block_alpha[j] + prefix_beta_v0 * one_block_beta[j];
				}
				else
				{
					ret_para[j] = ret_para[j] + prefix_alpha * one_block_alpha[j] + prefix_beta * one_block_beta[j];
				}
			}
		}
		if(!debug_mode)
			ret = ret_para;
	}
	if(!C.circuit[depth].is_parallel || debug_mode)
	{
		int first_half_g = C.circuit[depth].bit_length / 2;
		int second_half_g = C.circuit[depth].bit_length - first_half_g;
		int first_half_uv = C.circuit[depth - 1].bit_length / 2;
		int second_half_uv = C.circuit[depth - 1].bit_length - first_half_uv;

		prime_field::field_element *tmp_u_val;
		prime_field::field_element zero_v;
		zero_v = (beta_v_first_half[0] * beta_v_second_half[0] );
		bool relay_set = false;

		for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
		{
			int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
			
			int g_first_half = g & ((1 << first_half_g) - 1);
			int g_second_half = (g >> first_half_g);
			int u_first_half = u & ((1 << first_half_uv) - 1);
			int u_second_half = u >> first_half_uv;
			int v_first_half = v & ((1 << first_half_uv) - 1);
			int v_second_half = v >> first_half_uv;
			switch(C.circuit[depth].gates[i].ty)
			{
				case 0:
				{
					ret[0] = ret[0] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half])  * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half] );
					break;
				}
				case 1:
				{
					ret[1] = ret[1] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half])  * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half] );
					break;
				}
				case 2:
				{
					break;
				}
				case 3:
				{
					break;
				}
				case 4:
				{
					break;
				}
				case 5:
				{
					auto beta_g_val = beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half];
					auto beta_v_0 = beta_v_first_half[0] * beta_v_second_half[0];
					for(int j = u; j < v; ++j)
					{
						int u_first_half = j & ((1 << first_half_uv) - 1);
						int u_second_half = j >> first_half_uv;
						ret[5] = ret[5] + beta_g_val * beta_v_0 * (beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half]);
					}
					break;
				}
				case 6:
				{
					ret[6] = ret[6] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half])  * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half] );
					break;
				}
				case 7:
				{
					ret[7] = ret[7] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half])  * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half] );
					break;
				}
				case 8:
				{
					ret[8] = ret[8] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half])  * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half] );
					break;
				}
				case 9:
				{
					ret[9] = ret[9] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half])  * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half] );
					break;
				}
				case 10:
				{
					if(relay_set == false)
					{
						tmp_u_val = new prime_field::field_element[1 << C.circuit[depth - 1].bit_length];
						 
						for(int i = 0; i < (1 << C.circuit[depth - 1].bit_length); ++i)
						{
							int u_first_half = i & ((1 << first_half_uv) - 1);
							int u_second_half = i >> first_half_uv;
							tmp_u_val[i] = beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half];
						}

						relay_set = true;
					}
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					ret[10] = ret[10] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half])  * tmp_u_val[u];
					break;
				}
			}
		}
		
		ret[10] = ret[10] * zero_v;
	}
	for(int i = 0; i < 11; ++i)
	{
		if(C.circuit[depth].is_parallel)
			assert(ret[i] == ret_para[i]);
	}
	return ret;
}

bool verifier::verify()
{
	double v_time = 0;
	double pre_time = 0;
	std::chrono::high_resolution_clock::time_point v_t_a, v_t_b;
	prime_field::init_random();
	p -> proof_init();
	
	auto result = p -> evaluate();
	v_t_a = std::chrono::high_resolution_clock::now();
	prime_field::field_element alpha, beta;
	alpha = prime_field::field_element(1);
	beta = prime_field::field_element(0);
	random_oracle oracle;
	//initial random value
	prime_field::field_element *r_0 = generate_randomness(C.circuit[C.total_depth - 1].bit_length), *r_1 = generate_randomness(C.circuit[C.total_depth - 1].bit_length);
	prime_field::field_element *one_minus_r_0, *one_minus_r_1;
	one_minus_r_0 = new prime_field::field_element[C.circuit[C.total_depth - 1].bit_length];
	one_minus_r_1 = new prime_field::field_element[C.circuit[C.total_depth - 1].bit_length];

	for(int i = 0; i < (C.circuit[C.total_depth - 1].bit_length); ++i)
	{
		one_minus_r_0[i] = prime_field::field_element(1) - r_0[i];
		one_minus_r_1[i] = prime_field::field_element(1) - r_1[i];
	}
	v_t_b = std::chrono::high_resolution_clock::now();
	v_time += std::chrono::duration_cast<std::chrono::duration<double>>(v_t_b - v_t_a).count();
	std::chrono::high_resolution_clock::time_point t_a = std::chrono::high_resolution_clock::now();
	std::cerr << "Calc V_output(r)" << std::endl;
	prime_field::field_element a_0 = p -> V_res(one_minus_r_0, r_0, result, C.circuit[C.total_depth - 1].bit_length, (1 << (C.circuit[C.total_depth - 1].bit_length)));
	
	std::chrono::high_resolution_clock::time_point t_b = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> ts = std::chrono::duration_cast<std::chrono::duration<double>>(t_b - t_a);
	std::cerr << "	Time: " << ts.count() << std::endl;
	a_0 = alpha * a_0;

	prime_field::field_element alpha_beta_sum = a_0; //+ a_1
	prime_field::field_element direct_relay_value;

	//vpd staff
	//vpd_init();

	for(int i = C.total_depth - 1; i >= 1; --i)
	{
		std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
		std::cerr << "Bound u start" << std::endl;
		p -> sumcheck_init(i, C.circuit[i].bit_length, C.circuit[i - 1].bit_length, C.circuit[i - 1].bit_length, alpha, beta, r_0, r_1, one_minus_r_0, one_minus_r_1);
		p -> sumcheck_phase1_init();
		prime_field::field_element previous_random = prime_field::field_element(0);
		//next level random
		auto r_u = generate_randomness(C.circuit[i - 1].bit_length);
		auto r_v = generate_randomness(C.circuit[i - 1].bit_length);
		direct_relay_value = alpha * direct_relay(i, r_0, r_u) + beta * direct_relay(i, r_1, r_u);
		prime_field::field_element *one_minus_r_u, *one_minus_r_v;
		one_minus_r_u = new prime_field::field_element[C.circuit[i - 1].bit_length];
		one_minus_r_v = new prime_field::field_element[C.circuit[i - 1].bit_length];
		v_t_a = std::chrono::high_resolution_clock::now();
		
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			one_minus_r_u[j] = prime_field::field_element(1) - r_u[j];
			one_minus_r_v[j] = prime_field::field_element(1) - r_v[j];
		}
		v_t_b = std::chrono::high_resolution_clock::now();
		v_time += std::chrono::duration_cast<std::chrono::duration<double>>(v_t_b - v_t_a).count();
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			quadratic_poly poly = p -> sumcheck_phase1_update(previous_random, j);
			v_t_a = std::chrono::high_resolution_clock::now();
			previous_random = r_u[j];
			if(poly.eval(0) + poly.eval(1) != alpha_beta_sum)
			{
				fprintf(stderr, "Verification fail, phase1, circuit %d, current bit %d\n", i, j);
				return false;
			}
			else
			{
			}
			alpha_beta_sum = poly.eval(r_u[j]);
			v_t_b = std::chrono::high_resolution_clock::now();
			v_time += std::chrono::duration_cast<std::chrono::duration<double>>(v_t_b - v_t_a).count();
		}
		std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

		std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
		std::cerr << "	Time: " << time_span.count() << std::endl;
		
		std::cerr << "Bound v start" << std::endl;
		t0 = std::chrono::high_resolution_clock::now();
		p -> sumcheck_phase2_init(previous_random, r_u, one_minus_r_u);
		previous_random = prime_field::field_element(0);
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			if(i == 1)
				r_v[j] = prime_field::field_element(0);
			quadratic_poly poly = p -> sumcheck_phase2_update(previous_random, j);
			v_t_a = std::chrono::high_resolution_clock::now();
			previous_random = r_v[j];
			if(poly.eval(0) + poly.eval(1) + direct_relay_value * p -> v_u != alpha_beta_sum)
			{
				fprintf(stderr, "Verification fail, phase2, circuit level %d, current bit %d\n", i, j);
				return false;
			}
			else
			{
			}
			alpha_beta_sum = poly.eval(r_v[j]) + direct_relay_value * p -> v_u;
			v_t_b = std::chrono::high_resolution_clock::now();
			v_time += std::chrono::duration_cast<std::chrono::duration<double>>(v_t_b - v_t_a).count();
		}
		t1 = std::chrono::high_resolution_clock::now();
		time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
		std::cerr << "	Time: " << time_span.count() << std::endl;
		
		auto final_claims = p -> sumcheck_finalize(previous_random);
		auto v_u = final_claims.first;
		auto v_v = final_claims.second;
/*
		beta_init(i, alpha, beta, r_0, r_1, r_u, r_v, one_minus_r_0, one_minus_r_1, one_minus_r_u, one_minus_r_v);
		auto mult_value = mult(i);
		auto add_value = add(i);
		auto not_value = not_gate(i);
		auto minus_value = minus_gate(i);
		auto xor_value = xor_gate(i);
		auto naab_value = NAAB_gate(i);
		auto sum_value = sum_gate(i);
		auto relay_value = relay_gate(i);
*/		
		v_t_a = std::chrono::high_resolution_clock::now();
		beta_init(i, alpha, beta, r_0, r_1, r_u, r_v, one_minus_r_0, one_minus_r_1, one_minus_r_u, one_minus_r_v);
		auto predicates_value = predicates(i, r_0, r_1, r_u, r_v, alpha, beta);
		auto mult_value = predicates_value[1];
		auto add_value = predicates_value[0];
		auto not_value = predicates_value[6];
		auto minus_value = predicates_value[7];
		auto xor_value = predicates_value[8];
		auto naab_value = predicates_value[9];
		auto sum_value = predicates_value[5];
		auto relay_value = predicates_value[10];
		if(alpha_beta_sum != add_value * (v_u + v_v) + mult_value * v_u * v_v + direct_relay_value * v_u + not_value * (prime_field::field_element(1) - v_u) + minus_value * (v_u - v_v) + xor_value * (v_u + v_v - prime_field::field_element(2) * v_u * v_v) + naab_value * (v_v - v_u * v_v) + sum_value * v_u + relay_value * v_u)
		{
			fprintf(stderr, "Verification fail, semi final, circuit level %d\n", i);
			return false;
		}
		else
		{
			fprintf(stderr, "Verification Pass, semi final, circuit level %d\n", i);
		}
		v_t_b = std::chrono::high_resolution_clock::now();
		v_time += std::chrono::duration_cast<std::chrono::duration<double>>(v_t_b - v_t_a).count();
		pre_time += std::chrono::duration_cast<std::chrono::duration<double>>(v_t_b - v_t_a).count();
		auto tmp_alpha = generate_randomness(1), tmp_beta = generate_randomness(1);
		alpha = tmp_alpha[0];
		beta = tmp_beta[0];
		delete[] tmp_alpha;
		delete[] tmp_beta;
		if(i != 1)
			alpha_beta_sum = alpha * v_u + beta * v_v;
		else
		{
			alpha_beta_sum = v_u;
		}
		
		delete[] r_0;
		delete[] r_1;
		delete[] one_minus_r_0;
		delete[] one_minus_r_1;
		r_0 = r_u;
		r_1 = r_v;
		one_minus_r_0 = one_minus_r_u;
		one_minus_r_1 = one_minus_r_v;
		std::cerr << "Prove Time " << p -> total_time << std::endl;
	}

	//post sumcheck
	prime_field::field_element* input;
	input = new prime_field::field_element[(1 << C.circuit[0].bit_length)];

	for(int i = 0; i < (1 << C.circuit[0].bit_length); ++i)
	{
		int g = i;
		if(C.circuit[0].gates[g].ty == 3)
		{
			input[g] = prime_field::field_element(C.circuit[0].gates[g].u);
		}
		else if(C.circuit[0].gates[g].ty == 2)
		{
			input[g] = prime_field::field_element(0);
		}
		else
			assert(false);
	}

/*
	if(!verify_vpd(alpha_beta_sum, r_0, C.circuit[0].bit_length))
	{
		fprintf(stderr, "Verification fail, final input check fail.\n");
		return false;
	}
	else
	{
		fprintf(stderr, "Verification pass\n");
		std::cerr << "Prove Time " << p -> total_time << std::endl;
	}
 */
	auto input_0 = V_in(r_0, one_minus_r_0, input, C.circuit[0].bit_length, (1 << C.circuit[0].bit_length));
		// input_1 = V_in(r_1, one_minus_r_1, input, C.circuit[0].bit_length, (1 << C.circuit[0].bit_length));
 	
	delete[] input;
	delete[] r_0;
	delete[] r_1;
	delete[] one_minus_r_0;
	delete[] one_minus_r_1;

	if(alpha_beta_sum != input_0)
	{
		fprintf(stderr, "Verification fail, final input check fail.\n");
		return false;
	}
	else
	{
		fprintf(stderr, "Verification pass\n");
		//div 2 since double instance for SHA
		std::cerr << "Prove Time " << p -> total_time << std::endl;
		std::cerr << "Verification time: " << v_time << std::endl;
		std::cerr << "Verification predicate time: " << pre_time << std::endl;
	}
	

	p -> delete_self();
	delete_self();
	return true;
}

void verifier::delete_self()
{
	delete[] beta_g_r0;
	delete[] beta_g_r1;
	delete[] beta_u;
	delete[] beta_v;
	for(int i = 0; i < C.total_depth; ++i)
	{
		delete[] C.circuit[i].gates;
	}
	delete[] C.circuit;

	delete[] beta_g_r0_first_half;
	delete[] beta_g_r0_second_half;
	delete[] beta_g_r1_first_half;
	delete[] beta_g_r1_second_half;
	delete[] beta_u_first_half;
	delete[] beta_u_second_half;
	delete[] beta_v_first_half;
	delete[] beta_v_second_half;
	delete[] beta_g_r0_block_first_half;
	delete[] beta_g_r0_block_second_half;
	delete[] beta_g_r1_block_first_half;
	delete[] beta_g_r1_block_second_half;
	delete[] beta_u_block_first_half;
	delete[] beta_u_block_second_half;
	delete[] beta_v_block_first_half;
	delete[] beta_v_block_second_half;
}

//return the hhash array of commitments, randomness and final small polynomial (represented by rscode)
ldt_commitment verifier::commit_phase(int slice_num)
{
	v_time = 0;
	//assuming we already have the initial commit
	int codeword_size = (1 << (C.circuit[0].bit_length + rs_code_rate));
	//repeat until the codeword is constant
	__hhash_digest* ret = new __hhash_digest[C.circuit[0].bit_length + rs_code_rate];
	prime_field::field_element* randomness = new prime_field::field_element[C.circuit[0].bit_length + rs_code_rate];
	int ptr = 0;
	while(codeword_size > (1 << rs_code_rate))
	{
		randomness[ptr] = prime_field::random();
		ret[ptr] = p -> commit_phase_step(randomness[ptr], slice_num);
		codeword_size /= 2;
		ptr++;
	}
	ldt_commitment com;
	com.repeat_no = p -> current_repeat_no;
	com.commitment_hhash = ret;
	com.final_rs_code = p -> commit_phase_final(slice_num);
	com.randomness = randomness;
	com.mx_depth = ptr;
	return com;
}


inline bool verifier::verify_merkle(__hhash_digest h, __hhash_digest* merkle, int len, int pow, std::pair<prime_field::field_element, prime_field::field_element> value)
{
	__hhash_digest cur_hhash = merkle[len];
	__hhash_digest data[2];
	for(int i = 0; i < len; ++i)
	{
		data[0] = cur_hhash;
		data[1] = merkle[i];
		if((pow & 1))
		{
			data[0] = merkle[i];
			data[1] = cur_hhash;
		}
		pow /= 2;
		my_hhash(data, &cur_hhash);
	}
	memset(data, 0, sizeof data);
	prime_field::field_element v[2];
	v[0] = value.first;
	v[1] = value.second;
	data[0] = *((__hhash_digest*)(v));
	static __hhash_digest value_h;
	my_hhash(data, &value_h);
	return equals(h, cur_hhash) && equals(value_h, merkle[len]);
}

bool verifier::verify_phase(const ldt_commitment &com, int slice_num, int &delta_merkle_visited)
{
	if(com.mx_depth == 0)
	{
		//only initial commit and final rs code left
		//todo
		//code
		assert(false);
		return false;
	}
	//check consistency
//__asm__("INT $3;");
	std::chrono::high_resolution_clock::time_point t0, t1;
	std::chrono::duration<double> time_span;
	auto inv_2 = prime_field::inv(prime_field::field_element(2));
	std::pair<prime_field::field_element, std::pair<__hhash_digest*, int> > pre_alpha_1;
	std::pair<std::pair<prime_field::field_element, prime_field::field_element>, std::pair<__hhash_digest*, int> > alpha, beta;
	prime_field::field_element s0, s1, pre_y;
	prime_field::field_element root_of_unity;
	prime_field::field_element y;
	int total_merkle_visited = 0;
	bool equ_beta;
	for(int i = 0; i < com.mx_depth; ++i)
	{
	    t0 = std::chrono::high_resolution_clock::now();
		long long pow;
		if(i == 0)
		{
			do
			{
				pow = rand() % (1 << (C.circuit[0].bit_length + rs_code_rate - i));
			} while (pow < (1 << (C.circuit[0].bit_length - i)) || pow % 2 == 1);
			root_of_unity = prime_field::get_root_of_unity(C.circuit[0].bit_length + rs_code_rate - i);
			y = fast_pow(root_of_unity, pow);
		}
		else
		{
			root_of_unity = root_of_unity * root_of_unity;
			pow = pow % (1 << (C.circuit[0].bit_length + rs_code_rate - i));
			pre_y = y;
			y = y * y;
		}
		
		long long s0_pow, s1_pow;
		assert(pow % 2 == 0);
		s0_pow = pow / 2;
		s1_pow = (pow + (1LL << (C.circuit[0].bit_length + rs_code_rate - i))) / 2;
		s0 = fast_pow(root_of_unity, s0_pow);
		s1 = fast_pow(root_of_unity, s1_pow);
		int indicator;
		if(i != 0)
		{
			assert(s1 == pre_y || s0 == pre_y);
			if(s1 == pre_y)
				indicator = 1;
			else
				indicator = 0;
		}
		assert(s0 * s0 == y);
		assert(s1 * s1 == y);
		int new_size = 0;
		if(i == 0)
		{
			t1 = std::chrono::high_resolution_clock::now();
			time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
			v_time += time_span.count() * 3;
			alpha = p -> request_init_value_with_merkle(s0_pow, s1_pow, slice_num, new_size);

			total_merkle_visited += new_size * 2; //both h and p
	    	
			t0 = std::chrono::high_resolution_clock::now();
			assert(verify_merkle(vpd_com.slice_merkle_root[slice_num], alpha.second.first, alpha.second.second, min(s0_pow, s1_pow), alpha.first));
			t1 = std::chrono::high_resolution_clock::now();
			time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
			v_time += time_span.count() * 3;
			beta = p -> request_step_commit(0, pow / 2, com.repeat_no, slice_num, new_size);
			
			total_merkle_visited += new_size;
	    	
			t0 = std::chrono::high_resolution_clock::now();
			assert(verify_merkle(com.commitment_hhash[0], beta.second.first, beta.second.second, pow / 2, beta.first));
			
			auto inv_mu = prime_field::inv(fast_pow(root_of_unity, pow / 2));
			if(s0_pow > s1_pow)
				swap(alpha.first.first, alpha.first.second);
			auto p_val = (alpha.first.first + alpha.first.second) * inv_2 + (alpha.first.first - alpha.first.second) * inv_2 * com.randomness[i] * inv_mu;
			
			t1 = std::chrono::high_resolution_clock::now();
			time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
			v_time += time_span.count() * 3;
			delete[] alpha.second.first;
			if(p_val != beta.first.first && p_val != beta.first.second)
			{
				fprintf(stderr, "Fri check consistency first round fail\n");
				return false;
			}
			if(p_val == beta.first.first)
				equ_beta = false;
			else
				equ_beta = true;
		}
		else
		{
			t1 = std::chrono::high_resolution_clock::now();
			time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
			v_time += time_span.count();
			if(indicator == 1)
			{
				alpha = beta;
			}
			else
			{
				alpha = beta;
			}
			
			beta = p -> request_step_commit(i, pow / 2, com.repeat_no, slice_num, new_size);

			total_merkle_visited += new_size;
	    	
			t0 = std::chrono::high_resolution_clock::now();
			assert(verify_merkle(com.commitment_hhash[i], beta.second.first, beta.second.second, pow / 2, beta.first));

			auto inv_mu = prime_field::inv(fast_pow(root_of_unity, pow / 2));
			auto p_val_0 = (alpha.first.first + alpha.first.second) * inv_2 + (alpha.first.first - alpha.first.second) * inv_2 * com.randomness[i] * inv_mu;
			auto p_val_1 = (alpha.first.first + alpha.first.second) * inv_2 + (alpha.first.second - alpha.first.first) * inv_2 * com.randomness[i] * inv_mu;
			
			t1 = std::chrono::high_resolution_clock::now();
			time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
			v_time += time_span.count();
			delete[] alpha.second.first;
			if(p_val_0 != beta.first.first && p_val_0 != beta.first.second && p_val_1 != beta.first.first && p_val_1 != beta.first.second)
			{
				fprintf(stderr, "Fri check consistency %d round fail\n", i);
				return false;
			}
		}
	}
	delta_merkle_visited = total_merkle_visited;
	delete[] pre_alpha_1.second.first;
	//CHECK last rs code
	for(int i = 1; i < (1 << (rs_code_rate)); ++i)
	{
		if(p -> cpd[slice_num].rs_codeword[com.mx_depth - 1][i] != p -> cpd[slice_num].rs_codeword[com.mx_depth - 1][i - 1])
			return false;
	}
	return true;
}