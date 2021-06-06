#include "linear_gkr/zk_verifier.h"
#include <string>
#include <utility>
#include <vector>
#include <iostream>
#include "linear_gkr/random_generator.h"
#include "VPD/vpd_verifier.h"
#include "infrastructure/fiat_shamir.h"
using namespace std;
void zk_verifier::get_prover(zk_prover *pp)
{
	p = pp;
}

extern std::vector<prime_field::field_element> rou;

void zk_verifier::read_circuit(const char *path, const char *meta_path)
{
	int d;
	FILE *circuit_in;
	FILE *meta_in;

	meta_in = fopen(meta_path, "r");
	circuit_in = fopen(path, "r");

	fscanf(circuit_in, "%d", &d);
	int n;
	C.circuit = new layer[d + 1];
	C.total_depth = d + 1;
	int max_bit_length = -1;
	int n_pad;

	//estimate pad requirement
	int estimate_masks = 15 * 2 * log_num_degree + 4 * log_num_degree * log_num_verifier;

	int estimate_vector_inner_size = (estimate_masks + (1 << log_num_verifier));
	int pad_requirement;

	pad_requirement = 0;
	while(estimate_vector_inner_size != 0)
	{
		pad_requirement++;
		estimate_vector_inner_size /= 2;
	}
	pad_requirement++;
	

	for(int i = 1; i <= d; ++i)
	{
		fscanf(circuit_in, "%d", &n);
		if(i == 1 && n < (1 << pad_requirement))
		    n_pad = (1 << pad_requirement);
        else
            n_pad = n;
		if(i != 1)
		{
			if(n == 1)
				C.circuit[i].gates = new gate[2];
			else
				C.circuit[i].gates = new gate[n_pad];
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
				C.circuit[0].gates = new gate[n_pad];
				C.circuit[1].gates = new gate[n_pad];
			}
		}
		
		int max_gate = -1;
		int previous_g = -1;
		for(int j = 0; j < n; ++j)
		{
			int ty, g;
			long long u, v;
			fscanf(circuit_in, "%d%d%lld%lld", &ty, &g, &u, &v);
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
			if(ty == 13)
			{
				assert(u == v);
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

        if(i == 1)
        {
            for(int g = n; g < n_pad; ++g)
            {
                C.circuit[1].gates[g] = gate(4, g, 0);
                C.circuit[0].gates[g] = gate(3, 0, 0);
            }
            n = n_pad;
            previous_g = n_pad - 1;
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
		//fprintf(stderr, "layer %d, bit_length %d\n", i, C.circuit[i].bit_length);
		if(C.circuit[i].bit_length > max_bit_length)
			max_bit_length = C.circuit[i].bit_length;
	}
	C.circuit[0].is_parallel = false;
	for(int i = 1; i <= d; ++i)
	{
		int is_para;
		fscanf(meta_in, "%d", &is_para);
		fscanf(meta_in, "%d%d%d%d", &C.circuit[i].block_size, &C.circuit[i].repeat_num, &C.circuit[i].log_block_size, &C.circuit[i].log_repeat_num);
		if(is_para)
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
	
	C.circuit[0].is_all_direct_relay = true;

	for(int i = 1; i < C.total_depth; ++i)
	{
		C.circuit[i].is_all_direct_relay = true;
		for(int j = 0; j < (1 << C.circuit[i].bit_length); ++j)
		{
			if(C.circuit[i].gates[j].ty != 4)
			{
				C.circuit[i].is_all_direct_relay = false;
				break;
			}
		}
	}
	
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
	
	fclose(circuit_in);
	fclose(meta_in);
}

vector<prime_field::field_element> zk_verifier::predicates(int depth, prime_field::field_element *r_0, prime_field::field_element *r_1, prime_field::field_element *r_u, prime_field::field_element *r_v, prime_field::field_element alpha, prime_field::field_element beta)
{
	std::vector<prime_field::field_element> ret_para;
	std::vector<prime_field::field_element> ret;
	const int gate_type_count = 15;
	ret.resize(gate_type_count);
	ret_para.resize(gate_type_count);
	for(int i = 0; i < gate_type_count; ++i)
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
		int first_half_uv = C.circuit[depth - 1].log_block_size / 2;
		std::vector<prime_field::field_element> one_block_alpha, one_block_beta;
		one_block_alpha.resize(gate_type_count);
		one_block_beta.resize(gate_type_count);
		for(int i = 0; i < gate_type_count; ++i)
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
				case 12:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					
					auto beta_g_val_alpha = beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half];
					auto beta_g_val_beta = beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half];
					auto beta_v_0 = beta_v_block_first_half[0] * beta_v_block_second_half[0];
					for(int j = u; j <= v; ++j)
					{
						int u_first_half = j & ((1 << first_half_uv) - 1);
						int u_second_half = j >> first_half_uv;
						one_block_alpha[12] = one_block_alpha[12] + beta_g_val_alpha * beta_v_0 * (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half]);
						one_block_beta[12] = one_block_beta[12] + beta_g_val_beta * beta_v_0 * (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half]);

						beta_v_0 = beta_v_0 + beta_v_0;
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
				case 13:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					auto uv_value = (beta_u_block_first_half[u_first_half] * beta_u_block_second_half[u_second_half]) * (beta_v_block_first_half[v_first_half] * beta_v_block_second_half[v_second_half]);
					one_block_alpha[13] = one_block_alpha[13] + (beta_g_r0_block_first_half[g_first_half] * beta_g_r0_block_second_half[g_second_half]) * uv_value;
					one_block_beta[13] = one_block_beta[13] + (beta_g_r1_block_first_half[g_first_half] * beta_g_r1_block_second_half[g_second_half]) * uv_value;
					break;
				}
				case 14:
				{
					assert(false);
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
			for(int j = 0; j < gate_type_count; ++j)
			{
				if(j == 6 || j == 10 || j == 5 || j == 12)
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
		int first_half_uv = C.circuit[depth - 1].bit_length / 2;

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
				case 12:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					
					auto beta_g_val = beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half];
					auto beta_v_0 = beta_v_first_half[0] * beta_v_second_half[0];
					for(int j = u; j <= v; ++j)
					{
						int u_first_half = j & ((1 << first_half_uv) - 1);
						int u_second_half = j >> first_half_uv;
						ret[12] = ret[12] + beta_g_val * beta_v_0 * (beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half]);
						beta_v_0 = beta_v_0 + beta_v_0;
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
				case 13:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					int v_first_half = v & ((1 << first_half_uv) - 1);
					int v_second_half = v >> first_half_uv;
					ret[13] = ret[13] + (beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half]) * 
								(beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half]) * (beta_v_first_half[v_first_half] * beta_v_second_half[v_second_half]);
					break;
				}
				case 14:
				{
					int g_first_half = g & ((1 << first_half_g) - 1);
					int g_second_half = (g >> first_half_g);
					
					auto beta_g_val = beta_g_r0_first_half[g_first_half] * beta_g_r0_second_half[g_second_half] + beta_g_r1_first_half[g_first_half] * beta_g_r1_second_half[g_second_half];
					auto beta_v_0 = beta_v_first_half[0] * beta_v_second_half[0];
					int u_first_half = u & ((1 << first_half_uv) - 1);
					int u_second_half = u >> first_half_uv;
					
					ret[14] = ret[14] + beta_g_val * beta_v_0 * (beta_u_first_half[u_first_half] * beta_u_second_half[u_second_half]) * rou[v];
					break;
				}
			}
		}
		
		ret[10] = ret[10] * zero_v;
	}
	for(int i = 0; i < gate_type_count; ++i)
	{
		if(C.circuit[depth].is_parallel)
			assert(ret[i] == ret_para[i]);
	}
	return ret;
}

prime_field::field_element zk_verifier::direct_relay(int depth, prime_field::field_element *r_g, prime_field::field_element *r_u)
{
	if(!C.circuit[depth].is_all_direct_relay)
		return prime_field::field_element(0);
	else
	{
		prime_field::field_element ret = prime_field::field_element(1);
		for(int i = 0; i < C.circuit[depth].bit_length; ++i)
			ret = ret * (prime_field::field_element(1) - r_g[i] - r_u[i] + prime_field::field_element(2) * r_g[i] * r_u[i]);
		return ret;
	}
}

void zk_verifier::beta_init(int depth, prime_field::field_element alpha, prime_field::field_element beta,
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

prime_field::field_element zk_verifier::V_in(const prime_field::field_element* r_0, const prime_field::field_element* one_minus_r_0,
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

void zk_verifier::self_inner_product_test(prime_field::field_element alpha_beta_sum, prime_field::field_element v_in)
{
	//msk
	int v_mask_size = all_pub_mask.size();
	int p_mask_size = p -> all_pri_mask.size();
	//std::cout << "get into function" << std::endl;
	//printf("%d\n", v_mask_size);
	if(v_mask_size != p_mask_size){
		printf("%s\n", "size is different.");
	}
	prime_field::field_element sum = prime_field::field_element(0);
	for(int i = 0; i < v_mask_size; i++){
		sum = sum + all_pub_mask[i] * p -> all_pri_mask[i];
	}
	assert(sum == all_mask_sum);
	assert(v_in == alpha_beta_sum);
}
prime_field::field_element *q_eval_real;
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

prime_field::field_element *q_eval_verifier;
prime_field::field_element *q_ratio;
void dfs_ratio(int dep, prime_field::field_element val, prime_field::field_element *r, prime_field::field_element *one_minus_r, int pos)
{
    if(dep == log_slice_number)
        q_ratio[pos] = val;
    else
    {
        dfs_ratio(dep + 1, val * one_minus_r[log_slice_number - 1 - dep], r, one_minus_r, pos << 1);
		dfs_ratio(dep + 1, val * r[log_slice_number - 1 - dep], r, one_minus_r, pos << 1 | 1);
    }
}

void dfs_coef(int dep, prime_field::field_element val, prime_field::field_element *r, prime_field::field_element *one_minus_r, int pos, int r_len)
{
    if(dep == r_len)
        q_eval_verifier[pos] = val;
    else
    {
        dfs_coef(dep + 1, val * one_minus_r[r_len - 1 - dep], r, one_minus_r, pos << 1, r_len);
		dfs_coef(dep + 1, val * r[r_len - 1 - dep], r, one_minus_r, pos << 1 | 1, r_len);
    }
}

prime_field::field_element* public_array_prepare_generic(prime_field::field_element *public_array, int log_length)
{
	prime_field::field_element *q_coef_arr = new prime_field::field_element[1 << log_length];
	int coef_slice_size = (1 << (log_length - log_slice_number));
	for(int i = 0; i < (1 << log_slice_number); ++i)
	{
		inverse_fast_fourier_transform(&public_array[i * coef_slice_size], coef_slice_size, coef_slice_size, prime_field::get_root_of_unity(log_length - log_slice_number), &q_coef_arr[i * coef_slice_size]);
	}
	return q_coef_arr;
}

prime_field::field_element* public_array_prepare(prime_field::field_element *r, prime_field::field_element *one_minus_r, int log_length, prime_field::field_element *q_eval_real)
{
	q_eval_verifier = new prime_field::field_element[(1 << (log_length - log_slice_number))];
    q_ratio = new prime_field::field_element[(1 << log_slice_number) + 1];
    q_ratio[(1 << log_slice_number)] = prime_field::field_element(1);
    dfs_ratio(0, prime_field::field_element(1), r + log_length - log_slice_number, one_minus_r + log_length - log_slice_number, 0);
    dfs_coef(0, prime_field::field_element(1), r, one_minus_r, 0, log_length - log_slice_number);
    prime_field::field_element *q_coef_verifier = new prime_field::field_element[(1 << (log_length - log_slice_number))];
    inverse_fast_fourier_transform(q_eval_verifier, (1 << (log_length - log_slice_number)), (1 << (log_length - log_slice_number)), prime_field::get_root_of_unity(log_length - log_slice_number), q_coef_verifier);
	
	prime_field::field_element *q_coef_arr = new prime_field::field_element[1 << log_length];
	int coef_slice_size = (1 << (log_length - log_slice_number));
	for(int i = 0; i < (1 << log_slice_number); ++i)
	{
		for(int j = 0; j < coef_slice_size; ++j)
		{
			q_coef_arr[i * coef_slice_size + j] = q_coef_verifier[j] * q_ratio[i];
			assert(q_eval_real[i * coef_slice_size + j] == q_ratio[i] * q_eval_verifier[j]);
		}
	}
	delete[] q_coef_verifier;
	delete[] q_eval_verifier;
	delete[] q_ratio;
	return q_coef_arr;
}

bool zk_verifier::verify(const char* output_path)
{
	verifiers_fs.resize(1 << log_num_verifier);
	for(int i = 0; i < (1 << log_num_verifier); ++i)
	{
		verifiers_fs[i].randomize(rand());
	}
	//all_mask_sum = all_pub_mask * all_pri_mask;
	all_mask_sum = prime_field::field_element(0);
	double verification_time = 0;
	double predicates_calc_time = 0;
	double verification_rdl_time = 0;
	prime_field::init_random();
	p -> proof_init();

	auto result = p -> evaluate();

	auto output_t0 = std::chrono::high_resolution_clock::now();

	prime_field::field_element alpha, beta;
	alpha = prime_field::field_element(1);
	beta = prime_field::field_element(0);

	std::vector<prime_field::field_element> alpha_beta_sum_output_layer;
	std::vector<prime_field::field_element> r_0, one_minus_r_0, r_1, one_minus_r_1;
	std::vector<prime_field::field_element> r_u, one_minus_r_u, r_v, one_minus_r_v;
	//initial random value
	prime_field::field_element alpha_beta_sum;
	//output layer
	{
		std::vector<prime_field::field_element> real_output_layer;
		std::vector<prime_field::field_element> beta_multiplier;
		beta_multiplier.resize(1 << C.circuit[C.total_depth - 2].bit_length);
		real_output_layer.resize(1 << C.circuit[C.total_depth - 2].bit_length);
		alpha_beta_sum_output_layer.resize(1 << C.circuit[C.total_depth - 2].bit_length);
		for(int i = 0; i < (1 << C.circuit[C.total_depth - 2].bit_length); ++i)
		{
			real_output_layer[i] = p -> circuit_value[C.total_depth - 2][i];
			alpha_beta_sum_output_layer[i] = p -> circuit_value[C.total_depth - 2][i];
			beta_multiplier[i] = 1;
		}
		assert(C.circuit[C.total_depth - 1].bit_length == C.circuit[C.total_depth - 2].bit_length);
		for(int i = 0; i < C.circuit[C.total_depth - 1].bit_length; ++i)
		{
			linear_poly beta_part, v_part;
			std::vector<quadratic_poly> response;
			prime_field::field_element v_part_one = 0, v_part_zero = 0;
			prime_field::field_element beta_part_one = 0, beta_part_zero = 0;
			v_part = linear_poly(0, 0);
			response.resize(1 << log_num_verifier);
			int v_part_total_length = 1 << (C.circuit[C.total_depth - 1].bit_length - i);
			for(int j = 0; j < (1 << log_num_verifier); ++j)
			{
				response[j] = quadratic_poly(0, 0, 0);
			}
			for(int j = 0; j < v_part_total_length / 2; ++j)
			{
				v_part_one = real_output_layer[j << 1 | 1];
				v_part_zero = real_output_layer[j << 1];
				v_part.b = v_part_zero;
				v_part.a = v_part_one - v_part_zero;
				for(int k = 0; k < (1 << i); ++k)
				{
					//this bit is zero
					beta_part_one = 0;
					beta_part_zero = beta_multiplier[k];
					beta_part.b = beta_part_zero, beta_part.a = beta_part_one - beta_part_zero;
					response[j << (i + 1) | (0 << i) | k] = response[j << (i + 1) | (0 << i) | k] + v_part * beta_part;
					//this bit is one
					beta_part_zero = 0;
					beta_part_one = beta_multiplier[k];
					beta_part.b = beta_part_zero, beta_part.a = beta_part_one - beta_part_zero;
					response[j << (i + 1) | (1 << i) | k] = response[j << (i + 1) | (1 << i) | k] + v_part * beta_part;
				}
			}
			for(int j = 0; j < (1 << log_num_verifier); ++j)
			{
				assert(response[j].eval((j >> i) & 1) == alpha_beta_sum_output_layer[j]);
				verifiers_fs[j].update((const char*)&response[j], sizeof(quadratic_poly));
			}
			prime_field::field_element new_r;
			new_r = get_unified_hash(verifiers_fs.data(), 1 << log_num_verifier);
			r_u.push_back(new_r);
			one_minus_r_u.push_back(prime_field::field_element(1) - new_r);

			for(int k = 0; k < (1 << i); ++k)
			{
				beta_multiplier[k | (1 << i)] = beta_multiplier[k] * new_r;
				beta_multiplier[k] = beta_multiplier[k] * (prime_field::field_element(1) - new_r);
			}
			for(int j = 0; j < (1 << log_num_verifier); ++j)
			{
				alpha_beta_sum_output_layer[j] = response[j].eval(new_r);
			}
			if(v_part_total_length / 2 == 1)
			{
				alpha_beta_sum = v_part.eval(new_r);
			}
			for(int j = 0; j < v_part_total_length / 2; ++j)
			{
				v_part_one = real_output_layer[j << 1 | 1];
				v_part_zero = real_output_layer[j << 1];
				v_part.b = v_part_zero;
				v_part.a = v_part_one - v_part_zero;
				real_output_layer[j] = v_part.eval(new_r);
			}
		}
	}

	r_0 = r_u;
	r_1 = r_u;
	one_minus_r_0 = one_minus_r_u;
	one_minus_r_1 = one_minus_r_u;
	alpha = 1;
	beta = 0;
	prime_field::field_element direct_relay_value;

	auto output_t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(output_t1 - output_t0);
	p -> total_time += time_span.count();


	for(int i = C.total_depth - 2; i >= 1; --i)
	{
		//std::cerr << "Bound u start" << std::endl;
		auto rho = prime_field::field_element(0);

		p -> sumcheck_init(i, C.circuit[i].bit_length, C.circuit[i - 1].bit_length, C.circuit[i - 1].bit_length, alpha, beta, r_0.data(), r_1.data(), one_minus_r_0.data(), one_minus_r_1.data());
		p -> generate_maskpoly_pre_rho(C.circuit[i - 1].bit_length * 2 + 1, 2);
		p -> rho = rho;
		p -> generate_maskpoly_after_rho(C.circuit[i - 1].bit_length * 2 + 1, 2);	
		//add maskpoly

		alpha_beta_sum = (alpha_beta_sum + p->maskpoly_sumc);

		p -> sumcheck_phase1_init();
		prime_field::field_element previous_random = prime_field::field_element(0);
		//next level random
		auto r_u = verifiers_fs[0].get_rand(C.circuit[i - 1].bit_length);
		auto r_v = verifiers_fs[0].get_rand(C.circuit[i - 1].bit_length);
		direct_relay_value = alpha * direct_relay(i, r_0.data(), r_u.data()) + beta * direct_relay(i, r_1.data(), r_u.data());
		auto r_c = prime_field::field_element(0); //mem leak
		if(C.circuit[i].is_all_direct_relay){
			for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
				r_v[j] = prime_field::field_element(0);
			r_c = prime_field::field_element(0);
		}
		//V should test the maskR for two points, V does random linear combination of these points first
		auto random_combine = prime_field::field_element(0);

		auto linear_coeff = prime_field::field_element(0);
		//Add six public coeffs to the pub list all_pub_mask
		//maskR(g, c) = a_0 + a_1g + a_2g^2 + a_3c + a_4c^2 + a_5gc, g = preu1 or prev1
		all_pub_mask.push_back(prime_field::field_element(1) * random_combine + linear_coeff * prime_field::field_element(1) * random_combine);
		auto preu1 = p -> prepreu1;
		auto prev1 = p -> preprev1;
		all_pub_mask.push_back(preu1  * random_combine + linear_coeff * prev1 * random_combine);
		all_pub_mask.push_back(preu1 * preu1 * random_combine + linear_coeff * prev1 * prev1 * random_combine);
		all_pub_mask.push_back(r_c * random_combine + linear_coeff * r_c * random_combine);
		all_pub_mask.push_back(r_c * r_c * random_combine + linear_coeff * r_c * r_c * random_combine);
		all_pub_mask.push_back(preu1 * r_c * random_combine + linear_coeff * prev1 * r_c * random_combine);
		//Add maskpoly's public coefficient to all_pub_mask
		/*maskpoly = a_0u_0^2 + a_1u_0 + \cdots + a_{2n-2}u_{n-1}^2 + a_{2n-1}u_{n-1}  
				   + a_{2n}v_0^2 + a_{2n + 1}v_0 + \cdots + a_{4n-2}v_{n-1}^2 + a_{4n-1}v_{n-1}
				   + a_{4n}c^2 + a_{4n+1}c
				   + a_{4n + 2}(constant term)
				   //Here let m = 4n + 2, where n = bit_length in this layer
				   + a_{m + 1} * u_{n-1}^5 + a_{m + 2} * u_{n-1}^4 + a_{m + 3} * u_{n-1}^3
				   + a_{m + 4} * u_{n-1}^5 + a_{m + 5} * u_{n-1}^4 + a_{m + 6} * u_{n-1}^3
		*/

		//Every time all one test to V, V needs to do a linear combination for security.
		auto linear_combine = prime_field::field_element(0); //mem leak
		//a_0u_0^2 + a_1u_0 + \cdots + a_{2n-2}u_{n-1}^2 + a_{2n-1}u_{n-1}
		int ll = C.circuit[i - 1].bit_length;
		for(int k = 0; k < ll; k++){
			all_pub_mask.push_back(linear_combine * r_u[k] * r_u[k] * rho);
			all_pub_mask.push_back(linear_combine * r_u[k] * rho);
		}
		//a_{2n}v_0^2 + a_{2n + 1}v_0 + \cdots + a_{4n-2}v_{n-1}^2 + a_{4n-1}v_{n-1}
		for(int k = 0; k < ll; k++){
			all_pub_mask.push_back(linear_combine * r_v[k] * r_v[k] * rho);
			all_pub_mask.push_back(linear_combine * r_v[k] * rho);
		}
		//a_{4n}c^2 + a_{4n+1}c + a_{4n + 2}(constant term)
		all_pub_mask.push_back(linear_combine * r_c * r_c * rho);
		all_pub_mask.push_back(linear_combine * r_c * rho);
		all_pub_mask.push_back(linear_combine * prime_field::field_element(1) * rho);
		/*a_{m + 1} * u_{n-1}^5 + a_{m + 2} * u_{n-1}^4 + a_{m + 3} * u_{n-1}^3
		+ a_{m + 4} * u_{n-1}^5 + a_{m + 5} * u_{n-1}^4 + a_{m + 6} * u_{n-1}^3*/
		all_pub_mask.push_back(linear_combine * r_u[ll-1] * r_u[ll-1] * r_u[ll-1] * r_u[ll-1] * r_u[ll-1] * rho);
		all_pub_mask.push_back(linear_combine * r_u[ll-1] * r_u[ll-1] * r_u[ll-1] * r_u[ll-1] * rho);
		all_pub_mask.push_back(linear_combine * r_u[ll-1] * r_u[ll-1] * r_u[ll-1] * rho);
		all_pub_mask.push_back(linear_combine * r_v[ll-1] * r_v[ll-1] * r_v[ll-1] * r_v[ll-1] * r_v[ll-1] * rho);
		all_pub_mask.push_back(linear_combine * r_v[ll-1] * r_v[ll-1] * r_v[ll-1] * r_v[ll-1] * rho);
		all_pub_mask.push_back(linear_combine * r_v[ll-1] * r_v[ll-1] * r_v[ll-1] * rho);

		std::vector<prime_field::field_element> one_minus_r_u, one_minus_r_v;
		one_minus_r_u.resize(C.circuit[i - 1].bit_length);
		one_minus_r_v.resize(C.circuit[i - 1].bit_length);
		
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			one_minus_r_u[j] = prime_field::field_element(1) - r_u[j];
			one_minus_r_v[j] = prime_field::field_element(1) - r_v[j];
		}

		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{	
			if(j == C.circuit[i - 1].bit_length - 1){
				quintuple_poly poly = p->sumcheck_phase1_updatelastbit(previous_random, j);
				previous_random = r_u[j];


				if(poly.eval(0) + poly.eval(1) != alpha_beta_sum)
				{ 
					fprintf(stderr, "Verification fail, phase1, circuit %d, current bit %d\n", i, j);
					return false;
				}
				else
				{
					//fprintf(stderr, "Verification pass, phase1, circuit %d, current bit %d\n", i, j);
				}
				alpha_beta_sum = poly.eval(r_u[j]);

				for(int k = 0; k < (1 << log_num_verifier); ++k)
				{
					verifiers_fs[k].update((const char*)&poly, sizeof(quintuple_poly));
				}
			}

			else{
				quadratic_poly poly = p -> sumcheck_phase1_update(previous_random, j);
				previous_random = r_u[j];
			

				if(poly.eval(0) + poly.eval(1) != alpha_beta_sum)
				{
					fprintf(stderr, "Verification fail, phase1, circuit %d, current bit %d\n", i, j);
					return false;
				}
				else
				{
					//fprintf(stderr, "Verification pass, phase1, circuit %d, current bit %d\n", i, j);
				}
				alpha_beta_sum = poly.eval(r_u[j]);

				for(int k = 0; k < (1 << log_num_verifier); ++k)
				{
					verifiers_fs[k].update((const char*)&poly, sizeof(quadratic_poly));
				}
			}
		}
		
	//	std::cerr << "Bound v start" << std::endl;
		p -> sumcheck_phase2_init(previous_random, r_u.data(), one_minus_r_u.data());
		previous_random = prime_field::field_element(0);
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			if(C.circuit[i].is_all_direct_relay)
				r_v[j] = prime_field::field_element(0);
			if(j == C.circuit[i - 1].bit_length - 1){
				quintuple_poly poly = p -> sumcheck_phase2_updatelastbit(previous_random, j);
				poly.f = poly.f;
				previous_random = r_v[j];
				if(poly.eval(0) + poly.eval(1) + direct_relay_value * p -> v_u != alpha_beta_sum)
				{
					fprintf(stderr, "Verification fail, phase2, circuit level %d, current bit %d\n", i, j);
					return false;
				}
				else
				{
					//fprintf(stderr, "Verification pass, phase2, circuit level %d, current bit %d\n", i, j);
				}
				alpha_beta_sum = poly.eval(r_v[j]) + direct_relay_value * p -> v_u;

				for(int k = 0; k < (1 << log_num_verifier); ++k)
				{
					verifiers_fs[k].update((const char*)&poly, sizeof(quintuple_poly));
				}
			}
			else
			{
				quadratic_poly poly = p -> sumcheck_phase2_update(previous_random, j);
				poly.c = poly.c;
			
				previous_random = r_v[j];
				if(poly.eval(0) + poly.eval(1) + direct_relay_value * p -> v_u != alpha_beta_sum)
				{
					fprintf(stderr, "Verification fail, phase2, circuit level %d, current bit %d\n", i, j);
					return false;
				}
				else
				{
					//fprintf(stderr, "Verification pass, phase2, circuit level %d, current bit %d\n", i, j);
				}
				alpha_beta_sum = poly.eval(r_v[j]) + direct_relay_value * p -> v_u;


				for(int k = 0; k < (1 << log_num_verifier); ++k)
				{
					verifiers_fs[k].update((const char*)&poly, sizeof(quadratic_poly));
				}
			}
		}

	
		//Add one more round for maskR
		//quadratic_poly poly p->sumcheck_finalroundR(previous_random, C.current[i - 1].bit_length);
		
		auto final_claims = p -> sumcheck_finalize(previous_random);
		

		auto v_u = final_claims.first;
		auto v_v = final_claims.second;

		std::chrono::high_resolution_clock::time_point predicates_calc_t0 = std::chrono::high_resolution_clock::now();
		beta_init(i, alpha, beta, r_0.data(), r_1.data(), r_u.data(), r_v.data(), one_minus_r_0.data(), one_minus_r_1.data(), one_minus_r_u.data(), one_minus_r_v.data());
		auto predicates_value = predicates(i, r_0.data(), r_1.data(), r_u.data(), r_v.data(), alpha, beta);
		std::chrono::high_resolution_clock::time_point predicates_calc_t1 = std::chrono::high_resolution_clock::now();
		std::chrono::duration<double> predicates_calc_span = std::chrono::duration_cast<std::chrono::duration<double>>(predicates_calc_t1 - predicates_calc_t0);
		if(C.circuit[i].is_parallel == false)
			verification_rdl_time += predicates_calc_span.count();
		verification_time += predicates_calc_span.count();
		predicates_calc_time += predicates_calc_span.count();
		
		auto mult_value = predicates_value[1];
		auto add_value = predicates_value[0];
		auto not_value = predicates_value[6];
		auto minus_value = predicates_value[7];
		auto xor_value = predicates_value[8];
		auto naab_value = predicates_value[9];
		auto sum_value = predicates_value[5];
		auto relay_value = predicates_value[10];
		auto exp_sum_value = predicates_value[12];
		auto bit_test_value = predicates_value[13];
		auto rou_mult_value = predicates_value[14];
		quadratic_poly poly = p->sumcheck_finalround(previous_random, C.circuit[i - 1].bit_length << 1, add_value * (v_u + v_v) + mult_value * v_u * v_v + not_value * (prime_field::field_element(1) - v_u) + minus_value * (v_u - v_v) + xor_value * (v_u + v_v - prime_field::field_element(2) * v_u * v_v) + naab_value * (v_v - v_u * v_v) + sum_value * v_u + relay_value * v_u + rou_mult_value * v_u + exp_sum_value * v_u + bit_test_value * (v_u * (prime_field::field_element(1) - v_v)));

		for(int k = 0; k < (1 << log_num_verifier); ++k)
		{
			verifiers_fs[k].update((const char*)&poly, sizeof(quadratic_poly));
		}
		
		if(poly.eval(0) + poly.eval(1) + direct_relay_value * v_u != alpha_beta_sum)
		{
			fprintf(stderr, "Verification fail, phase2, lastbit for c\n");
			return false;
		}
		if(C.circuit[i].is_all_direct_relay)
			r_c = prime_field::field_element(0);
		alpha_beta_sum = poly.eval(r_c) + direct_relay_value * p -> v_u;

		std::vector<prime_field::field_element> r;
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
			r.push_back(r_u[j]);
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
			r.push_back(r_v[j]);
		r.push_back(r_c);
		
		prime_field::field_element maskpoly_value = p -> query(r_u.data(), r_v.data(), r_c);
		prime_field::field_element maskRg1_value = p -> queryRg1(r_c);
		prime_field::field_element maskRg2_value = p -> queryRg2(r_c);
		//here we do linear combination for all_mask_sum correspondingly.

		//prime_field::field_element test_mask_sum = linear_combine * maskpoly_value;
		all_mask_sum = all_mask_sum + maskRg1_value  * random_combine + linear_coeff * maskRg2_value * random_combine + linear_combine * maskpoly_value;
	
		if(alpha_beta_sum != r_c * (add_value * (v_u + v_v) + mult_value * v_u * v_v + not_value * (prime_field::field_element(1) - v_u) + minus_value * (v_u - v_v) + xor_value * (v_u + v_v - prime_field::field_element(2) * v_u * v_v) + naab_value * (v_v - v_u * v_v) + sum_value * v_u + relay_value * v_u + rou_mult_value * v_u + exp_sum_value * v_u + bit_test_value * (prime_field::field_element(1) - v_v) * v_u) + alpha * p -> Iuv * p ->preZu * maskRg1_value + beta * p -> Iuv * p -> preZv * maskRg2_value + maskpoly_value + direct_relay_value * v_u)
		{
			fprintf(stderr, "Verification fail, semi final, circuit level %d\n", i);
			return false;
		}
		else
		{
		}
		auto tmp_alpha = verifiers_fs[0].get_rand(1), tmp_beta = verifiers_fs[0].get_rand(1);
		alpha = tmp_alpha[0];
		beta = tmp_beta[0];
		if(i != 1)
			alpha_beta_sum = alpha * v_u + beta * v_v;
		else
			alpha_beta_sum = v_u;
		r_0 = r_u;
		r_1 = r_v;
		one_minus_r_0 = one_minus_r_u;
		one_minus_r_1 = one_minus_r_v;
	}

	//post sumcheck
	all_pub_mask.push_back(p->Zu);
	all_pub_mask.push_back(p->Zu * p->preu1);
	p->all_pri_mask.push_back(p->maskr[0]);
	p->all_pri_mask.push_back(p->maskr[1]);
	all_mask_sum = all_mask_sum + p->Zu * p->sumRc.eval(p->preu1);
	
	std::cerr << "GKR Prove Time " << p -> total_time << std::endl;
	prime_field::field_element *all_sum;
	all_sum = new prime_field::field_element[slice_number + 1];
	auto merkle_root_l = (p -> poly_prover).commit_private_array(p -> circuit_value[0], C.circuit[0].bit_length, p -> all_pri_mask);
	
	q_eval_real = new prime_field::field_element[1 << C.circuit[0].bit_length];
	dfs_for_public_eval(0, prime_field::field_element(1), r_0.data(), one_minus_r_0.data(), C.circuit[0].bit_length, 0);
	auto merkle_root_h = (p -> poly_prover).commit_public_array(all_pub_mask, q_eval_real, C.circuit[0].bit_length, alpha_beta_sum - p->Zu * p->sumRc.eval(p->preu1) + all_mask_sum, all_sum);
	
	for(int i = 0; i < (1 << log_num_verifier); ++i)
	{
		verifiers_fs[i].update((const char*)&merkle_root_l, sizeof(__hhash_digest));
		verifiers_fs[i].update((const char*)&merkle_root_h, sizeof(__hhash_digest));
	}

	poly_ver.p = &(p -> poly_prover);
	
	prime_field::field_element *public_array = public_array_prepare(r_0.data(), one_minus_r_0.data(), C.circuit[0].bit_length, q_eval_real);
	//prime_field::field_element *public_array = public_array_prepare_generic(q_eval_real, C.circuit[0].bit_length);
	
	bool input_0_verify = poly_ver.verify_poly_commitment(all_sum, C.circuit[0].bit_length, public_array, all_pub_mask, verification_time, p -> total_time, merkle_root_l, merkle_root_h, verifiers_fs);
	delete[] q_eval_real;
	p -> total_time += (p -> poly_prover).total_time;
	if(!(input_0_verify))
	{
		fprintf(stderr, "Verification fail, input vpd.\n");
		return false;
	}
	else
	{
		fprintf(stderr, "Verification pass\n");
		std::cerr << "Prove Time " << p -> total_time << std::endl;
		std::cerr << "Verification rdl time " << verification_rdl_time << std::endl;
		//verification rdl time is the non-parallel part of the circuit. In all of our experiments and most applications, it can be calculated in O(log n) or O(log^2 n) time. We didn't implement the fast method due to the deadline.
		std::cerr << "Verification Time " << verification_time - verification_rdl_time << std::endl;
		verifiers_fs[0].output("v0_proof.bin");
		FILE *result = fopen(output_path, "w");
		fprintf(result, "%lf %lf %d\n", p -> total_time, verification_time - verification_rdl_time, verifiers_fs[0].transcript.size());
		fclose(result);
	}
	p -> delete_self();
	delete_self();
	return true;
}

void zk_verifier::delete_self()
{
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
	for(int i = 0; i < C.total_depth; ++i)
	{
		delete[] C.circuit[i].gates;
	}
	delete[] C.circuit;
}
