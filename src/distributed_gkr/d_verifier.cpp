#include "linear_gkr/d_verifier.h"
#include <string>
#include <utility>
#include <vector>
#include <iostream>
#include "linear_gkr/random_generator.h"
#include "VPD/vpd_verifier.h"

using namespace std;
void zk_verifier::get_prover(zk_prover *pp)
{
	p = pp;
}

void zk_verifier::read_r1cs(const char* A_path, const char* B_path, const char* C_path, const char* witness, const char *meta_path)
{
	long long nA, nB, nC, n;
	FILE* A_ptr = fopen(A_path, "rb");
	FILE* B_ptr = fopen(B_path, "rb");
	FILE* C_ptr = fopen(C_path, "rb");

	fread(&nA, sizeof(long long), 1, A_ptr);
	fread(&nB, sizeof(long long), 1, B_ptr);
	fread(&nC, sizeof(long long), 1, C_ptr);

	assert(nA == nB && nA == nC);
	n = nA;
	long long *idx_row_A = new long long[n];
	long long *idx_row_B = new long long[n];
	long long *idx_row_C = new long long[n];
	long long *idx_col_A = new long long[n];
	long long *idx_col_B = new long long[n];
	long long *idx_col_C = new long long[n];

	prime_field::field_element *A_val = new prime_field::field_element[n];
	prime_field::field_element *B_val = new prime_field::field_element[n];
	prime_field::field_element *C_val = new prime_field::field_element[n];
	prime_field::field_element *witness_val = new prime_field::field_element[n];


	for(int i = 0; i < n; ++i)
	{
		fread(&idx_row_A[i], sizeof(long long), 1, A_ptr);
		fread(&idx_col_A[i], sizeof(long long), 1, A_ptr);
		fread(&A_val[i].value.lo, sizeof(__uint128_t), 1, A_ptr);
		fread(&A_val[i].value.mid, sizeof(__uint128_t), 1, A_ptr);

		fread(&idx_row_B[i], sizeof(long long), 1, B_ptr);
		fread(&idx_col_B[i], sizeof(long long), 1, B_ptr);
		fread(&B_val[i].value.lo, sizeof(__uint128_t), 1, B_ptr);
		fread(&B_val[i].value.mid, sizeof(__uint128_t), 1, B_ptr);

		fread(&idx_row_C[i], sizeof(long long), 1, C_ptr);
		fread(&idx_col_C[i], sizeof(long long), 1, C_ptr);
		fread(&C_val[i].value.lo, sizeof(__uint128_t), 1, C_ptr);
		fread(&C_val[i].value.mid, sizeof(__uint128_t), 1, C_ptr);
	}


	FILE *witness_ptr = fopen(witness, "r");
	long long witness_count = 0;
	
	while(!feof(witness_ptr))
	{
		char id[1024], num[1024];
		fscanf(witness_ptr, "%s %s", id, num);
		prime_field::u256b val = prime_field::u256b(num, strlen(num), 10);
		witness_val[witness_count].value = val;
		witness_count++;
	}
	long long witness_count_padded = 1;
	while(witness_count_padded < witness_count)
	{
		witness_count_padded *= 2;
	}


	
	C.circuit = new layer[5]; //input layer + relay layer + (A * z, B * z, C * z) layer + elements wise product layer + output layer
	C.total_depth = 5;

	{
		C.circuit[0].bit_length = mylog(witness_count_padded);
		//C.circuit[0].is_parallel = 0;
		//C.circuit[0].block_size = 1;
		//write relay layer and input layer
		for(int i = 0; i < witness_count; ++i)
		{
			C.inputs[i] = witness[i];
		}
		for(int i = witness_count; i < witness_count_padded; ++i)
		{
			C.inputs[i] = prime_field::field_element(0);
		}

		C.circuit[1].bit_length = mylog(witness_count_padded);
		//C.circuit[1].is_parallel = 0;
		//C.circuit[1].block_size = 1;
		C.circuit[1].gates = new gate[witness_count_padded];

	}


	
	fclose(witness_ptr);
	fclose(A_ptr);
	fclose(B_ptr);
	fclose(C_ptr);
	delete[] idx_row_A;
	delete[] idx_row_B;
	delete[] idx_row_C;
	delete[] idx_col_A;
	delete[] idx_col_B;
	delete[] idx_col_C;
	delete[] A_val;
	delete[] B_val;
	delete[] C_val;
	delete[] witness_val;

}

#ifdef MPI_ENABLED
void zk_verifier::set_rank(int r, int size)
{
	rank = r;
	mpi_world_size = size;
}
#endif

void zk_verifier::read_witness(const char* path_prefix, int rank)
{
	char path[256];
	sprintf(path, "%s_%d", path_prefix, rank);
	printf("Reading witness %s %d\n", path, rank);

	FILE *witness_in = fopen(path, "r");

	//read witness
	long long log_witness_count = C.circuit[0].bit_length;
	long long witness_count = 1 << log_witness_count;

	C.inputs = new prime_field::field_element[witness_count];
	for(int i = 0; i < witness_count; ++i)
	{
		char num[1024];
		fscanf(witness_in, "%s", num);
		prime_field::u512b val = prime_field::u512b(num, strlen(num), 10);
		C.inputs[i].value = val;
	}

	fclose(witness_in);
}

void zk_verifier::read_circuit(const char *circuit_path, const char *meta_path)
{
	int d;
	FILE *circuit_in, *witness_in;
	FILE *meta_in;

	meta_in = fopen(meta_path, "r");
	circuit_in = fopen(circuit_path, "r");

	fscanf(circuit_in, "%d", &d);
	int n;
	C.circuit = new layer[d + 1];
	C.total_depth = d + 1;
	int max_bit_length = -1;
	int n_pad;
	for(int i = 1; i <= d; ++i)
	{
	    int pad_requirement = 1 << log_slice_number;
		fscanf(circuit_in, "%d", &n);
		if(i == 1 && n < (1 << pad_requirement))
		    n_pad = max(2, (1 << pad_requirement));
        else
            n_pad = max(2, n);
		if(i == 1)
		{
			C.circuit[0].gates = new gate[n_pad];
		}
		C.circuit[i].gates = new gate[n_pad];
		
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
		fprintf(stderr, "layer %d, bit_length %d\n", i, C.circuit[i].bit_length);
		if(C.circuit[i].bit_length > max_bit_length)
			max_bit_length = C.circuit[i].bit_length;
	}
	/*
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
	*/
	
	
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

vector<prime_field::field_element> zk_verifier::predicates(int depth, prime_field::field_element *r_0, prime_field::field_element *r_1, prime_field::field_element *r_u, prime_field::field_element *r_v, prime_field::field_element alpha, prime_field::field_element beta, int lg_world)
{
	//std::vector<prime_field::field_element> ret_para;
	std::vector<prime_field::field_element> ret;
	const int gate_type_count = 14;
	ret.resize(gate_type_count);
	//ret_para.resize(gate_type_count);
	for(int i = 0; i < gate_type_count; ++i)
	{
		ret[i] = prime_field::field_element(0);
		//ret_para[i] = prime_field::field_element(0);
	}
	if(depth == 1)
	{
		return ret;
	}
	bool debug_mode = false;
	/*
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
	*/
	//if(!C.circuit[depth].is_parallel || debug_mode)
	std::vector<prime_field::field_element> one_block_alpha, one_block_beta;
	one_block_alpha.resize(gate_type_count);
	one_block_beta.resize(gate_type_count);
	{
		int first_half_g = C.circuit[depth].bit_length / 2;
		int first_half_uv = C.circuit[depth - 1].bit_length / 2;

		prime_field::field_element *tmp_u_val;
		prime_field::field_element zero_v;
		zero_v = (beta_v_first_half[0] * beta_v_second_half[0]);
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
			}
		}
		
		ret[10] = ret[10] * zero_v;
	}

	auto one = prime_field::field_element(1);
	for(int i = 0; i < (1 << lg_world); ++i)
	{
		prime_field::field_element prefix_alpha, prefix_beta;
		prime_field::field_element prefix_alpha_v0, prefix_beta_v0;
		prefix_alpha = one;
		prefix_beta = one;
		prefix_alpha_v0 = one;
		prefix_beta_v0 = one;
		for(int j = 0; j < lg_world; ++j)
		{
			if((i >> j) & 1)
			{
				auto uv_value = r_u[j + C.circuit[depth - 1].bit_length] * r_v[j + C.circuit[depth - 1].bit_length];
				prefix_alpha = prefix_alpha * r_0[j + C.circuit[depth].bit_length] * uv_value;
				prefix_beta = prefix_beta * r_1[j + C.circuit[depth].bit_length] * uv_value;
			}
			else
			{
				auto uv_value = (one - r_u[j + C.circuit[depth - 1].bit_length]) * (one - r_v[j + C.circuit[depth - 1].bit_length]);
				prefix_alpha = prefix_alpha * (one - r_0[j + C.circuit[depth].bit_length]) * uv_value;
				prefix_beta = prefix_beta * (one - r_1[j + C.circuit[depth].bit_length]) * uv_value;
			}
		}
		for(int j = 0; j < lg_world; ++j)
		{
			if((i >> j) & 1)
			{
				auto uv_value = r_u[j + C.circuit[depth - 1].bit_length] * (one - r_v[j + C.circuit[depth - 1].bit_length]);
				prefix_alpha_v0 = prefix_alpha_v0 * r_0[j + C.circuit[depth].bit_length] * uv_value;
				prefix_beta_v0 = prefix_beta_v0 * r_1[j + C.circuit[depth].bit_length] * uv_value;
			}
			else
			{
				auto uv_value = (one - r_u[j + C.circuit[depth - 1].bit_length]) * (one - r_v[j + C.circuit[depth - 1].bit_length]);
				prefix_alpha_v0 = prefix_alpha_v0 * (one - r_0[j + C.circuit[depth].bit_length]) * uv_value;
				prefix_beta_v0 = prefix_beta_v0 * (one - r_1[j + C.circuit[depth].bit_length]) * uv_value;
			}
		}
		for(int j = 0; j < gate_type_count; ++j)
		{
			if(j == 6 || j == 10 || j == 5 || j == 12)
			{
				ret[j] = ret[j] + prefix_alpha_v0 * one_block_alpha[j] + prefix_beta_v0 * one_block_beta[j];
			}
			else
			{
				ret[j] = ret[j] + prefix_alpha * one_block_alpha[j] + prefix_beta * one_block_beta[j];
			}
		}
	}

	/*
	for(int i = 0; i < gate_type_count; ++i)
	{
		if(C.circuit[depth].is_parallel)
			assert(ret[i] == ret_para[i]);
	}
	*/
	return ret;
}

prime_field::field_element zk_verifier::direct_relay(int depth, prime_field::field_element *r_g, prime_field::field_element *r_u, const int lg_world)
{
	if(depth != 1)
		return prime_field::field_element(0);
	else
	{
		prime_field::field_element ret = prime_field::field_element(1);
		for(int i = 0; i < C.circuit[depth].bit_length + lg_world; ++i)
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
    q_ratio = new prime_field::field_element[(1 << log_slice_number)];
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

prime_field::field_element summarize_results(prime_field::field_element *r, prime_field::field_element *one_minus_r, int lg_world_size, int lg_n, int rank, prime_field::field_element self_result)
{
	printf("summarize_results, rank = %d, self_res = %s\n", rank, self_result.to_string());
	
	MPI_Barrier(MPI_COMM_WORLD);
	//combine the result
	auto tmp_store = self_result;
	if(rank == 0)
	{
		int mpi_world_size = 1 << lg_world_size;
		prime_field::field_element *result = new prime_field::field_element[mpi_world_size];
		result[0] = self_result;
		for(int i = 1; i < mpi_world_size; ++i)
		{
			MPI_Recv(&result[i], 1, mpifield_element_t, i, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
		}
		int output_size = 1 << lg_world_size;
		for(int i = 0; i < lg_world_size; ++i)
		{
			for(int j = 0; j < (output_size >> 1); ++j)
			{
				result[j] = (result[j << 1] * one_minus_r[i + lg_n] + result[j << 1 | 1] * r[i + lg_n]);
			}
			output_size >>= 1;
		}
		self_result = result[0];
		//assert(self_result != tmp_store);
		for(int i = 1; i < mpi_world_size; ++i)
		{
			MPI_Send(&self_result, 1, mpifield_element_t, i, 0, MPI_COMM_WORLD);
		}
		delete[] result;
	}
	else
	{
		//send a_0 to master and receive accumlated result
		MPI_Send(&self_result, 1, mpifield_element_t, 0, 0, MPI_COMM_WORLD);
		MPI_Recv(&self_result, 1, mpifield_element_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	}
	MPI_Barrier(MPI_COMM_WORLD);
	printf("summarize_results done\n");
	return self_result;
}

quadratic_poly summarize_poly(quadratic_poly poly, int lg_world_size, int rank)
{
	MPI_Barrier(MPI_COMM_WORLD);
	quadratic_poly result;
	result.a = 0;
	result.b = 0;
	result.c = 0;
	
	prime_field::field_element *a, *b, *c;
	a = b = c = NULL;
	if(rank == 0)
	{
		a = new prime_field::field_element[1 << lg_world_size];
		b = new prime_field::field_element[1 << lg_world_size];
		c = new prime_field::field_element[1 << lg_world_size];
	}
	printf("Doing MPI Gather on %d machines\n", 1 << lg_world_size);
	MPI_Gather(&poly.a, 1, mpifield_element_t, a, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Gather(&poly.b, 1, mpifield_element_t, b, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Gather(&poly.c, 1, mpifield_element_t, c, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	printf("Done MPI Gather\n");
	if(rank == 0)
	{
		for(int i = 0; i < (1 << lg_world_size); ++i)
		{
			printf("a[%d] = %s\n", i, a[i].to_string());
			printf("b[%d] = %s\n", i, b[i].to_string());
			printf("c[%d] = %s\n", i, c[i].to_string());
			result.a = result.a + a[i];
			result.b = result.b + b[i];
			result.c = result.c + c[i];
		}
		delete[] a;
		delete[] b;
		delete[] c;
	}

	MPI_Bcast(&result.a, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Bcast(&result.b, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Bcast(&result.c, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Barrier(MPI_COMM_WORLD);
	return result;
}
#include <unistd.h>
prime_field::field_element zk_verifier::leader_gather_and_continue_sumcheck(linear_poly V_mult_add, linear_poly addV_array, linear_poly add_mult_sum, prime_field::field_element alpha_beta_sum, prime_field::field_element &previous_random, prime_field::field_element* r, int lg_n, int rank, int lg_world, int &proof_size)
{
	printf("Leader gather and continue sumcheck on %d machines %d\n", 1 << lg_world, rank);
	
	MPI_Barrier(MPI_COMM_WORLD);
	linear_poly *V_mult_add_array;
	linear_poly *addV_array_array;
	linear_poly *add_mult_sum_array;

	if(rank == 0)
	{
		V_mult_add_array = new linear_poly[1 << lg_world];
		addV_array_array = new linear_poly[1 << lg_world];
		add_mult_sum_array = new linear_poly[1 << lg_world];
	}

	fflush(stdout);
	
	MPI_Gather(&V_mult_add, 1, mpilinear_poly_t, V_mult_add_array, 1, mpilinear_poly_t, 0, MPI_COMM_WORLD);
	MPI_Gather(&addV_array, 1, mpilinear_poly_t, addV_array_array, 1, mpilinear_poly_t, 0, MPI_COMM_WORLD);
	MPI_Gather(&add_mult_sum, 1, mpilinear_poly_t, add_mult_sum_array, 1, mpilinear_poly_t, 0, MPI_COMM_WORLD);
	printf("Done MPI Gather on linear poly %d\n", rank);
	MPI_Barrier(MPI_COMM_WORLD);
	if(rank == 0)
	{
		printf("Leader doing stuff\n");
		p -> total_uv = (1 << lg_world);
		prime_field::field_element test_res = prime_field::field_element(0);
		for(int i = 0; i < (1 << lg_world); ++i)
		{
			p -> V_mult_add[i] = V_mult_add_array[i];
			p -> addV_array[i] = addV_array_array[i];
			p -> add_mult_sum[i] = add_mult_sum_array[i];
			auto tmp = add_mult_sum_array[i] * V_mult_add_array[i];
			tmp.b = tmp.b + addV_array_array[i].a;
			tmp.c = tmp.c + addV_array_array[i].b;
			test_res = test_res + tmp.eval(previous_random);
		}
		printf("Test result = %d, lg_n = %d\n", (int)(test_res == alpha_beta_sum), lg_n);
		for(int i = 0; i < lg_world; ++i)
		{
			printf("Start sumcheck update generic\n");
			quadratic_poly poly = p -> sumcheck_phase_update_generic(previous_random, i + lg_n);

			proof_size += sizeof(quadratic_poly);
			previous_random = r[i + lg_n];

			if(poly.eval(0) + poly.eval(1) != alpha_beta_sum)
			{
				printf("Verification fail, phase1, in master node, current bit %d\n", i);
				assert(false);
			}
			else
			{
				printf("Verification pass, phase1, in master node, current bit %d\n", i);
			}
			alpha_beta_sum = poly.eval(r[i + lg_n]);
		}
		printf("Leader calculation done\n");
	}
	MPI_Barrier(MPI_COMM_WORLD);
	printf("start bcast\n");
	MPI_Bcast(&alpha_beta_sum, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Barrier(MPI_COMM_WORLD);
	MPI_Bcast(&p -> V_mult_add[0], 1, mpilinear_poly_t, 0, MPI_COMM_WORLD);
	MPI_Barrier(MPI_COMM_WORLD);
	MPI_Bcast(&p -> addV_array[0], 1, mpilinear_poly_t, 0, MPI_COMM_WORLD);
	MPI_Barrier(MPI_COMM_WORLD);
	MPI_Bcast(&p -> add_mult_sum[0], 1, mpilinear_poly_t, 0, MPI_COMM_WORLD);
	MPI_Barrier(MPI_COMM_WORLD);
	MPI_Bcast(&previous_random, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
	MPI_Barrier(MPI_COMM_WORLD);
	return alpha_beta_sum;
}

bool zk_verifier::verify(const char* output_path)
{
	printf("Verifying proof...\n");
	int lg_world = mylog(mpi_world_size);
	int proof_size = 0;
	//there is a way to compress binlinear pairing element
	double verification_time = 0;
	double predicates_calc_time = 0;
	double verification_rdl_time = 0;
	prime_field::init_random();
	p -> proof_init();

	auto result = p -> evaluate();

	prime_field::field_element alpha, beta;
	alpha = prime_field::field_element(1);
	beta = prime_field::field_element(0);
	random_oracle oracle;
	//initial random value
	
	prime_field::field_element *r_0 = generate_randomness(C.circuit[C.total_depth - 1].bit_length + lg_world), *r_1 = generate_randomness(C.circuit[C.total_depth - 1].bit_length + lg_world);
	if(rank == 0) //master node
	{
		//send r_0, r_1 to everyone
		for(int i = 1; i < mpi_world_size; ++i)
		{
			MPI_Send(r_0, C.circuit[C.total_depth - 1].bit_length + lg_world, mpifield_element_t, i, 0, MPI_COMM_WORLD);
			MPI_Send(r_1, C.circuit[C.total_depth - 1].bit_length + lg_world, mpifield_element_t, i, 0, MPI_COMM_WORLD);
		}
		
	}
	else
	{
		MPI_Recv(r_0, C.circuit[C.total_depth - 1].bit_length + lg_world, mpifield_element_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
		MPI_Recv(r_1, C.circuit[C.total_depth - 1].bit_length + lg_world, mpifield_element_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	}
	prime_field::field_element *one_minus_r_0, *one_minus_r_1;
	one_minus_r_0 = new prime_field::field_element[C.circuit[C.total_depth - 1].bit_length + lg_world];
	one_minus_r_1 = new prime_field::field_element[C.circuit[C.total_depth - 1].bit_length + lg_world];

	for(int i = 0; i < (C.circuit[C.total_depth - 1].bit_length + lg_world); ++i)
	{
		one_minus_r_0[i] = prime_field::field_element(1) - r_0[i];
		one_minus_r_1[i] = prime_field::field_element(1) - r_1[i];
	}
	
	std::chrono::high_resolution_clock::time_point t_a = std::chrono::high_resolution_clock::now();
	std::cerr << "Calc V_output(r)" << std::endl;
	prime_field::field_element a_0 = p -> V_res(one_minus_r_0, r_0, result, C.circuit[C.total_depth - 1].bit_length, (1 << (C.circuit[C.total_depth - 1].bit_length)));
	std::chrono::high_resolution_clock::time_point t_b = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> ts = std::chrono::duration_cast<std::chrono::duration<double>>(t_b - t_a);
	std::cerr << "	Time: " << ts.count() << std::endl;
	a_0 = alpha * a_0;
	printf("prior summarize %s\n", a_0.to_string());
	a_0 = summarize_results(r_0, one_minus_r_0, lg_world, C.circuit[C.total_depth - 1].bit_length, rank, a_0);
	printf("after summarize %s\n", a_0.to_string());

	//a_0 is the result of the last layer of the whole circuit now

	prime_field::field_element alpha_beta_sum = a_0; //+ a_1

	prime_field::field_element direct_relay_value;
	for(int i = C.total_depth - 1; i >= 1; --i)
	{
		std::cerr << "Bound u start" << std::endl;

		p -> sumcheck_init(i, C.circuit[i].bit_length, C.circuit[i - 1].bit_length, C.circuit[i - 1].bit_length, alpha, beta, r_0, r_1, one_minus_r_0, one_minus_r_1);
		printf("sumcheck init start\n");
		MPI_Barrier(MPI_COMM_WORLD);
		p -> sumcheck_phase1_init();
		MPI_Barrier(MPI_COMM_WORLD);
		printf("sumcheck init done\n");
		prime_field::field_element previous_random = prime_field::field_element(0);
		//next level random
		MPI_Barrier(MPI_COMM_WORLD);
		prime_field::field_element *r_u;
		prime_field::field_element *r_v;
		if(rank == 0)
		{
			r_u = generate_randomness(C.circuit[i - 1].bit_length + lg_world);
			r_v = generate_randomness(C.circuit[i - 1].bit_length + lg_world);
		}
		else
		{
			r_u = new prime_field::field_element[C.circuit[i - 1].bit_length + lg_world];
			r_v = new prime_field::field_element[C.circuit[i - 1].bit_length + lg_world];
		}
		MPI_Bcast(r_u, C.circuit[i - 1].bit_length + lg_world, mpifield_element_t, 0, MPI_COMM_WORLD);
		MPI_Bcast(r_v, C.circuit[i - 1].bit_length + lg_world, mpifield_element_t, 0, MPI_COMM_WORLD);
		MPI_Barrier(MPI_COMM_WORLD);
		printf("randomnes sharing done\n");
		direct_relay_value = alpha * direct_relay(i, r_0, r_u, lg_world) + beta * direct_relay(i, r_1, r_u, lg_world);
		if(i == 1){
			for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
				r_v[j] = prime_field::field_element(0);
		}
		printf("direct relay done\n");
		prime_field::field_element *one_minus_r_u, *one_minus_r_v;
		printf("malloc size %d\n", C.circuit[i - 1].bit_length + lg_world);
		one_minus_r_u = new prime_field::field_element[C.circuit[i - 1].bit_length + lg_world];
		one_minus_r_v = new prime_field::field_element[C.circuit[i - 1].bit_length + lg_world];
		
		for(int j = 0; j < C.circuit[i - 1].bit_length + lg_world; ++j)
		{
			one_minus_r_u[j] = prime_field::field_element(1) - r_u[j];
			one_minus_r_v[j] = prime_field::field_element(1) - r_v[j];
		}

		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{	
			MPI_Barrier(MPI_COMM_WORLD);
			printf("sumcheck phase1 update start\n");
			quadratic_poly poly = p -> sumcheck_phase1_update(previous_random, j);
			printf("sumcheck phase1 update done\n");
			MPI_Barrier(MPI_COMM_WORLD);
			poly = summarize_poly(poly, lg_world, rank);
			printf("summarize poly done\n");
			MPI_Barrier(MPI_COMM_WORLD);
			proof_size += sizeof(quadratic_poly);
			previous_random = r_u[j];

			if(poly.eval(0) + poly.eval(1) != alpha_beta_sum)
			{
				fprintf(stderr, "Verification fail, phase1, circuit %d, current bit %d\n", i, j);
				return false;
			}
			else
			{
				fprintf(stderr, "Verification pass, phase1, circuit %d, current bit %d\n", i, j);
			}
			alpha_beta_sum = poly.eval(r_u[j]);
		}
		MPI_Barrier(MPI_COMM_WORLD);
		printf("Phase 1 complete\n");
		//leader node accumlate the result and continue the sumcheck phase 1
		printf("rank %d, prior leader gather sum %s\n", rank, alpha_beta_sum.to_string());
		assert(p -> total_uv == 1);
		alpha_beta_sum = leader_gather_and_continue_sumcheck(p -> V_mult_add[0], p -> addV_array[0], p -> add_mult_sum[0], alpha_beta_sum, previous_random, r_u, C.circuit[i - 1].bit_length, rank, lg_world, proof_size);
		printf("rank %d, after leader gather sum %s\n", rank, alpha_beta_sum.to_string());
		printf("rank %d finished leader gather\n", rank);
		MPI_Barrier(MPI_COMM_WORLD);
		std::cerr << "Bound v start" << std::endl;
		p -> sumcheck_phase2_init(previous_random, r_u, one_minus_r_u);
		printf("rank %d, sumcheck phase2 init done\n", rank);
		fflush(stdout);
		MPI_Barrier(MPI_COMM_WORLD);
		previous_random = prime_field::field_element(0);
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			if(i == 1)
				r_v[j] = prime_field::field_element(0);
			quadratic_poly poly = p -> sumcheck_phase2_update(previous_random, j);
			MPI_Barrier(MPI_COMM_WORLD);
			poly = summarize_poly(poly, lg_world, rank);
			proof_size += sizeof(quadratic_poly);
			
			previous_random = r_v[j];
			if(poly.eval(0) + poly.eval(1) + direct_relay_value * p -> v_u != alpha_beta_sum)
			{
				fprintf(stderr, "Verification fail, phase2, circuit level %d, current bit %d\n", i, j);
				return false;
			}
			else
			{
				fprintf(stderr, "Verification pass, phase2, circuit level %d, current bit %d\n", i, j);
			}
			alpha_beta_sum = poly.eval(r_v[j]) + direct_relay_value * p -> v_u;
		}

		//leader node accumlate the result and continue the sumcheck phase 2
		alpha_beta_sum = leader_gather_and_continue_sumcheck(p -> V_mult_add[0], p -> addV_array[0], p -> add_mult_sum[0], alpha_beta_sum, previous_random, r_v, C.circuit[i - 1].bit_length, rank, lg_world, proof_size);

		auto final_claims = p -> sumcheck_finalize(previous_random);
		

		auto v_u = final_claims.first;
		auto v_v = final_claims.second;

		std::chrono::high_resolution_clock::time_point predicates_calc_t0 = std::chrono::high_resolution_clock::now();
		beta_init(i, alpha, beta, r_0, r_1, r_u, r_v, one_minus_r_0, one_minus_r_1, one_minus_r_u, one_minus_r_v);
		auto predicates_value = predicates(i, r_0, r_1, r_u, r_v, alpha, beta, lg_world);

		std::chrono::high_resolution_clock::time_point predicates_calc_t1 = std::chrono::high_resolution_clock::now();
		std::chrono::duration<double> predicates_calc_span = std::chrono::duration_cast<std::chrono::duration<double>>(predicates_calc_t1 - predicates_calc_t0);
		//if(C.circuit[i].is_parallel == false)
		//	verification_rdl_time += predicates_calc_span.count();
		verification_time += predicates_calc_span.count();
		predicates_calc_time += predicates_calc_span.count();
		
		auto add_value = predicates_value[0];
		auto mult_value = predicates_value[1];
		auto sum_value = predicates_value[5];
		auto not_value = predicates_value[6];
		auto minus_value = predicates_value[7];
		auto xor_value = predicates_value[8];
		auto naab_value = predicates_value[9];
		auto relay_value = predicates_value[10];
		auto exp_sum_value = predicates_value[12];
		auto bit_test_value = predicates_value[13];
		
	
		if(alpha_beta_sum != (add_value * (v_u + v_v) + mult_value * v_u * v_v + not_value * (prime_field::field_element(1) - v_u) + minus_value * (v_u - v_v) + xor_value * (v_u + v_v - prime_field::field_element(2) * v_u * v_v) + naab_value * (v_v - v_u * v_v) + sum_value * v_u + relay_value * v_u + exp_sum_value * v_u + bit_test_value * (prime_field::field_element(1) - v_v) * v_u) + direct_relay_value * v_u)
		{
			fprintf(stderr, "Verification fail, semi final, circuit level %d\n", i);
			return false;
		}
		
		if(rank == 0)
		{
			auto tmp_alpha = generate_randomness(1), tmp_beta = generate_randomness(1);
			alpha = tmp_alpha[0];
			beta = tmp_beta[0];
			delete[] tmp_alpha;
			delete[] tmp_beta;
		}
		MPI_Bcast(&alpha, 1, mpifield_element_t, 0, MPI_COMM_WORLD);
		MPI_Bcast(&beta, 1, mpifield_element_t, 0, MPI_COMM_WORLD);

		if(i != 1)
			alpha_beta_sum = alpha * v_u + beta * v_v;
		else
			alpha_beta_sum = v_u;
		delete[] r_0;
		delete[] r_1;
		delete[] one_minus_r_0;
		delete[] one_minus_r_1;
		r_0 = r_u;
		r_1 = r_v;
		one_minus_r_0 = one_minus_r_u;
		one_minus_r_1 = one_minus_r_v;
	}

	std::cerr << "GKR Prove Time fff " << p -> total_time << std::endl;

	return true;

	prime_field::field_element *all_sum;
	all_sum = new prime_field::field_element[slice_number];
	auto merkle_root_l = (p -> poly_prover).commit_private_array(p -> circuit_value[0], C.circuit[0].bit_length);
	
	q_eval_real = new prime_field::field_element[1 << C.circuit[0].bit_length];
	dfs_for_public_eval(0, prime_field::field_element(1), r_0, one_minus_r_0, C.circuit[0].bit_length, 0);
	auto merkle_root_h = (p -> poly_prover).commit_public_array(q_eval_real, C.circuit[0].bit_length, alpha_beta_sum, all_sum);
	
	proof_size += 2 * sizeof(__hhash_digest);
	VPD_randomness = r_0;
	one_minus_VPD_randomness = one_minus_r_0;
	poly_ver.p = &(p -> poly_prover);
	
	prime_field::field_element *public_array = public_array_prepare(r_0, one_minus_r_0, C.circuit[0].bit_length, q_eval_real);
	//prime_field::field_element *public_array = public_array_prepare_generic(q_eval_real, C.circuit[0].bit_length);
	
	bool input_0_verify = poly_ver.verify_poly_commitment(all_sum, C.circuit[0].bit_length, public_array, verification_time, proof_size, p -> total_time, merkle_root_l, merkle_root_h);
	delete[] q_eval_real;
	delete[] r_0;
	delete[] r_1;
	delete[] one_minus_r_0;
	delete[] one_minus_r_1;
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
		std::cerr << "Proof size(bytes) " << proof_size << std::endl;
		FILE *result = fopen(output_path, "w");
		fprintf(result, "%lf %lf %lf %lf %d\n", p -> total_time, verification_time, predicates_calc_time, verification_rdl_time, proof_size);
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
}
