#include "linear_gkr/zk_verifier.h"
#include "infrastructure/RS_polynomial.h"
#include "infrastructure/utility.h"
#include "linear_gkr/zk_prover.h"
#include <iostream>
#include <cstdio>
inline bool verify_merkle(__hhash_digest h, std::vector<__hhash_digest> merkle_path, int len, int pow, std::vector<std::pair<prime_field::field_element, prime_field::field_element> > value)
{
	__hhash_digest cur_hhash = merkle_path[len - 1];
	__hhash_digest data[2];
	for(int i = 0; i < len - 1; ++i)
	{
		data[0] = cur_hhash;
		data[1] = merkle_path[i];
		if((pow & 1))
		{
			data[0] = merkle_path[i];
			data[1] = cur_hhash;
		}
		pow /= 2;
		my_hhash(data, &cur_hhash);
	}
	memset(data, 0, sizeof data);
    assert(value.size() % 2 == 1);
	__hhash_digest value_h;
    memset(&value_h, 0, sizeof(__hhash_digest));
    for(int i = 0; i < value.size(); ++i)
    {
        prime_field::field_element data_ele[2];
        data_ele[0] = value[i].first;
        data_ele[1] = value[i].second;
        memcpy(&data[0], data_ele, sizeof(__hhash_digest));
        data[1] = value_h;
        my_hhash(data, &value_h);
        unsigned long long *h0, *h1;
        h0 = (unsigned long long *)&value_h.h0;
        h1 = (unsigned long long *)&value_h.h1;
    }
	return equals(h, cur_hhash) && equals(value_h, merkle_path[len - 1]);
}

prime_field::field_element *q_coef_verifier, *q_ratio, *q_eval_verifier;
prime_field::field_element *mask_q_coef;

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

//return the hhash array of commitments, randomness and final small polynomial (represented by rscode)
ldt_commitment zk_verifier::commit_phase()
{
    //Prover do the work
    std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
    auto log_current_witness_size_per_slice_cp = fri::log_current_witness_size_per_slice;
	//assuming we already have the initial commit
	int codeword_size = (1 << (C.circuit[0].bit_length + rs_code_rate - log_slice_number));
	//repeat until the codeword is constant
	__hhash_digest* ret = new __hhash_digest[C.circuit[0].bit_length + rs_code_rate - log_slice_number];
	prime_field::field_element* randomness = new prime_field::field_element[C.circuit[0].bit_length + rs_code_rate];
	int ptr = 0;
	while(codeword_size > (1 << rs_code_rate))
	{
        assert(ptr < C.circuit[0].bit_length + rs_code_rate - log_slice_number);
		randomness[ptr] = prime_field::random();
		ret[ptr] = fri::commit_phase_step(randomness[ptr]);
		codeword_size /= 2;
		ptr++;
	}
	ldt_commitment com;
	com.commitment_hhash = ret;
	com.final_rs_code = fri::commit_phase_final();
	com.randomness = randomness;
	com.mx_depth = ptr;
    fri::log_current_witness_size_per_slice = log_current_witness_size_per_slice_cp;

    std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	p -> total_time += time_span.count();
	printf("Commit time %lf\n", time_span.count());

	return com;
}

bool zk_verifier::vpd_verify(prime_field::field_element* all_sum, double &v_time, int &proof_size, double &p_time, __hhash_digest merkle_tree_l, __hhash_digest merkle_tree_h)
{
    auto all_pub_msk_arr = new prime_field::field_element[all_pub_mask.size()];
	for(int i = 0; i < all_pub_mask.size(); ++i)
		all_pub_msk_arr[i] = all_pub_mask[i];
	prime_field::field_element *all_pub_msk_coef = new prime_field::field_element[all_pub_mask.size()];
    inverse_fast_fourier_transform(all_pub_msk_arr, all_pub_mask.size(), all_pub_mask.size(), prime_field::get_root_of_unity(mylog(all_pub_mask.size())), all_pub_msk_coef);
	
    //prepare ratio and array q
    char *command = new char[1024];
    sprintf(command, "./fft_gkr %d log_fftgkr.txt", C.circuit[0].bit_length - log_slice_number);
    system(command);
    FILE *fft_gkr_result = fopen("log_fftgkr.txt", "r");
    float v_time_fft, p_time_fft;
    int proof_size_fft;
    fscanf(fft_gkr_result, "%f%d%f", &v_time_fft,&proof_size_fft,&p_time_fft);
    v_time += v_time_fft;
    p_time += p_time_fft;
    proof_size += proof_size_fft;
    fclose(fft_gkr_result);

    q_eval_verifier = new prime_field::field_element[(1 << (C.circuit[0].bit_length - log_slice_number))];
    q_ratio = new prime_field::field_element[(1 << log_slice_number) + 1];
    q_ratio[(1 << log_slice_number)] = prime_field::field_element(1);
    dfs_ratio(0, prime_field::field_element(1), VPD_randomness + C.circuit[0].bit_length - log_slice_number, one_minus_VPD_randomness + C.circuit[0].bit_length - log_slice_number, 0);
    dfs_coef(0, prime_field::field_element(1), VPD_randomness, one_minus_VPD_randomness, 0, C.circuit[0].bit_length - log_slice_number);
    q_coef_verifier = new prime_field::field_element[(1 << (C.circuit[0].bit_length - log_slice_number))];
    inverse_fast_fourier_transform(q_eval_verifier, (1 << (C.circuit[0].bit_length - log_slice_number)), (1 << (C.circuit[0].bit_length - log_slice_number)), prime_field::get_root_of_unity(C.circuit[0].bit_length - log_slice_number), q_coef_verifier);

    auto com = commit_phase();

    for(int rep = 0; rep < 33; ++rep)
    {
        int slice_count = 1 << log_slice_number;
        slice_count++; //for masks
        int slice_size = (1 << (C.circuit[0].bit_length + rs_code_rate - log_slice_number));

        std::chrono::high_resolution_clock::time_point t0, t1;
        std::chrono::duration<double> time_span;
        auto inv_2 = prime_field::inv(prime_field::field_element(2));
        std::pair<prime_field::field_element, std::pair<__hhash_digest*, int> > pre_alpha_1;
        std::pair<std::vector<std::pair<prime_field::field_element, prime_field::field_element> >, std::vector<__hhash_digest> > alpha_l, alpha_h, alpha, beta_l, beta_h, beta;
        prime_field::field_element s0, s1, pre_y;
        prime_field::field_element root_of_unity;
        prime_field::field_element y;
        bool equ_beta;
        assert(C.circuit[0].bit_length - log_slice_number > 0);
        long long pow;
        for(int i = 0; i < C.circuit[0].bit_length - log_slice_number; ++i)
        {
            t0 = std::chrono::high_resolution_clock::now();
            if(i == 0)
            {
                do
                {
                    pow = rand() % (1 << (C.circuit[0].bit_length + rs_code_rate - log_slice_number - i));
                } while (pow < (1 << (C.circuit[0].bit_length - log_slice_number - i)) || pow % 2 == 1);
                root_of_unity = prime_field::get_root_of_unity(C.circuit[0].bit_length + rs_code_rate - log_slice_number - i);
                y = fast_pow(root_of_unity, pow);
            }
            else
            {
                root_of_unity = root_of_unity * root_of_unity;
                pow = pow % (1 << (C.circuit[0].bit_length + rs_code_rate - log_slice_number - i));
                pre_y = y;
                y = y * y;
            }
            long long s0_pow, s1_pow;
            assert(pow % 2 == 0);
            s0_pow = pow / 2;
            s1_pow = (pow + (1LL << (C.circuit[0].bit_length + rs_code_rate - log_slice_number - i))) / 2;
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
                v_time += time_span.count();
                alpha_l = fri::request_init_value_with_merkle(s0_pow, s1_pow, new_size, 0);
                alpha_h = fri::request_init_value_with_merkle(s0_pow, s1_pow, new_size, 1);

                proof_size += new_size; //both h and p
                
                t0 = std::chrono::high_resolution_clock::now();
                if(!verify_merkle(merkle_tree_l, alpha_l.second, alpha_l.second.size(), min(s0_pow, s1_pow), alpha_l.first))
                    return false;
                if(!verify_merkle(merkle_tree_h, alpha_h.second, alpha_h.second.size(), min(s0_pow, s1_pow), alpha_h.first))
                    return false;
                t1 = std::chrono::high_resolution_clock::now();
                time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
                v_time += time_span.count();
                beta = fri::request_step_commit(0, pow / 2, new_size);

                proof_size += new_size;
                
                t0 = std::chrono::high_resolution_clock::now();
                if(!verify_merkle(com.commitment_hhash[0], beta.second, beta.second.size(), pow / 2, beta.first))
                    return false;
                
                auto inv_mu = prime_field::inv(fast_pow(root_of_unity, pow / 2));
                alpha.first.clear(), alpha.second.clear();
                int mask_position_gap = slice_size / all_pub_mask.size();
                prime_field::field_element rou[2], x[2], inv_x[2], msk_rou[2];
                x[0] = prime_field::get_root_of_unity(mylog(slice_size));
                x[1] = prime_field::get_root_of_unity(mylog(slice_size));
                x[0] = prime_field::fast_pow(x[0], s0_pow);
                x[1] = prime_field::fast_pow(x[1], s1_pow);
                msk_rou[0] = prime_field::fast_pow(x[0], slice_size / mask_position_gap);
                msk_rou[1] = prime_field::fast_pow(x[1], slice_size / mask_position_gap);
                rou[0] = prime_field::fast_pow(x[0], slice_size >> rs_code_rate);
                rou[1] = prime_field::fast_pow(x[1], slice_size >> rs_code_rate);
                inv_x[0] = prime_field::inv(x[0]);
                inv_x[1] = prime_field::inv(x[1]);
                prime_field::field_element inv_msk_H;
                prime_field::field_element inv_H;
                inv_msk_H = prime_field::inv(prime_field::field_element(slice_size / mask_position_gap));
                inv_H = prime_field::inv(prime_field::field_element(slice_size >> rs_code_rate));
                alpha.first.resize(slice_count);

                prime_field::field_element q_eval_0_msk, q_eval_1_msk, x0, x1;
                prime_field::field_element q_eval_0_val, q_eval_1_val;
                q_eval_0_msk = q_eval_1_msk = prime_field::field_element(0);
                q_eval_0_val = q_eval_1_val = prime_field::field_element(0);
                x0 = x1 = prime_field::field_element(1);
                for(int k = 0; k < (1 << (C.circuit[0].bit_length - log_slice_number)); ++k)
                {
                    q_eval_0_val = q_eval_0_val + x0 * q_coef_verifier[k]; x0 = x0 * x[0];
                    q_eval_1_val = q_eval_1_val + x1 * q_coef_verifier[k]; x1 = x1 * x[1];
                }
                x0 = x1 = prime_field::field_element(1);
                for(int k = 0; k < all_pub_mask.size(); ++k)
                {
                    q_eval_0_msk = q_eval_0_msk + x0 * all_pub_msk_coef[k]; x0 = x0 * x[0];
                    q_eval_1_msk = q_eval_1_msk + x1 * all_pub_msk_coef[k]; x1 = x1 * x[1];
                }
                for(int j = 0; j < slice_count; ++j)
                {
                    prime_field::field_element q_eval_0 = prime_field::field_element(0), x0 = prime_field::field_element(1);
                    prime_field::field_element q_eval_1 = prime_field::field_element(0), x1 = prime_field::field_element(1);
                    if(j != slice_count - 1)
                    {
                        q_eval_0 = q_eval_0_val;
                        q_eval_1 = q_eval_1_val;
                    }
                    else
                    {
                        q_eval_0 = q_eval_0_msk;
                        q_eval_1 = q_eval_1_msk;
                    }
                    auto one = prime_field::field_element(1);
                    //merge l and h
                    if(j == slice_count - 1)
                    {
                        alpha.first[j].first = alpha_l.first[j].first * q_eval_0 - (msk_rou[0] - one) * alpha_h.first[j].first;
                        alpha.first[j].first = (alpha.first[j].first * prime_field::field_element(slice_size / mask_position_gap) - all_sum[j]) * inv_x[0];
                        alpha.first[j].second = alpha_l.first[j].second * q_eval_1 - (msk_rou[1] - one) * alpha_h.first[j].second;
                        alpha.first[j].second = (alpha.first[j].second * prime_field::field_element(slice_size / mask_position_gap) - all_sum[j]) * inv_x[1];
                    }
                    else
                    {
                        alpha.first[j].first = alpha_l.first[j].first * q_eval_0 * q_ratio[j] - (rou[0] - one) * alpha_h.first[j].first;
                        alpha.first[j].first = (alpha.first[j].first * prime_field::field_element(slice_size >> rs_code_rate) - all_sum[j]) * inv_x[0];
                        alpha.first[j].second = alpha_l.first[j].second * q_eval_1 * q_ratio[j] - (rou[1] - one) * alpha_h.first[j].second;
                        alpha.first[j].second = (alpha.first[j].second * prime_field::field_element(slice_size >> rs_code_rate) - all_sum[j]) * inv_x[1];
                    }
                    if(s0_pow > s1_pow)
                        std::swap(alpha.first[j].first, alpha.first[j].second);
                    auto p_val = (alpha.first[j].first + alpha.first[j].second) * inv_2 + (alpha.first[j].first - alpha.first[j].second) * inv_2 * com.randomness[i] * inv_mu;
                    
                    if(p_val != beta.first[j].first && p_val != beta.first[j].second)
                    {
                        fprintf(stderr, "Fri check consistency first round fail\n");
                        return false;
                    }
                    if(p_val == beta.first[j].first)
                        equ_beta = false;
                    else
                        equ_beta = true;
                }
                
                t1 = std::chrono::high_resolution_clock::now(); 
                time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
                //This will not added into v time since the fft gkr already give the result, we didn't have time to integrate the fft gkr into the main body, so we have the evaluation code here
                //v_time += time_span.count();
            }
            else
            {
                t1 = std::chrono::high_resolution_clock::now();
                time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
                v_time += time_span.count();
               // std::cerr << "Verification Time " << v_time << std::endl;
                if(indicator == 1)
                {
                    alpha = beta;
                }
                else
                {
                    alpha = beta;
                }
                
                beta = fri::request_step_commit(i, pow / 2, new_size);

                proof_size += new_size;
                
                t0 = std::chrono::high_resolution_clock::now();
                if(!verify_merkle(com.commitment_hhash[i], beta.second, beta.second.size(), pow / 2, beta.first))
                    return false;

                auto inv_mu = prime_field::inv(fast_pow(root_of_unity, pow / 2));
                t1 = std::chrono::high_resolution_clock::now();
                time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
                v_time += time_span.count();
                for(int j = 0; j < slice_count; ++j)
                {
                    auto p_val_0 = (alpha.first[j].first + alpha.first[j].second) * inv_2 + (alpha.first[j].first - alpha.first[j].second) * inv_2 * com.randomness[i] * inv_mu;
                    auto p_val_1 = (alpha.first[j].first + alpha.first[j].second) * inv_2 + (alpha.first[j].second - alpha.first[j].first) * inv_2 * com.randomness[i] * inv_mu;
                    if(p_val_0 != beta.first[j].first && p_val_0 != beta.first[j].second && p_val_1 != beta.first[j].first && p_val_1 != beta.first[j].second)
                    {
                        fprintf(stderr, "Fri check consistency %d round fail\n", i);
                        return false;
                    }
                }
            }
        }
        delete[] pre_alpha_1.second.first;
        //CHECK last rs code
        for(int i = 0; i < slice_count - 1; ++i)
        {
            auto tmplate = fri::cpd.rs_codeword[com.mx_depth - 1][0 << (log_slice_number + 1) | i << 1 | 0];
            for(int j = 0; j < (1 << (rs_code_rate - 1)); ++j)
            {
                if(fri::cpd.rs_codeword[com.mx_depth - 1][j << (log_slice_number + 1) | i << 1 | 0] != tmplate)
                {
                    fprintf(stderr, "Fri rs code check fail\n");
                    return false;
                }
            }
        }
        for(int j = 1; j < (1 << rs_code_rate); ++j)
            if(fri::cpd.rs_codeword_msk[com.mx_depth - 1][j] != fri::cpd.rs_codeword_msk[com.mx_depth - 1][j - 1])
            {
                fprintf(stderr, "Fri msk rs code check fail\n");
                return false;
            }
    }
    return true;
}