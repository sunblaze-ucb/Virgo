#include "infrastructure/RS_polynomial.h"
#include <thread>
#include <iostream>
prime_field::field_element* __dst[3];
prime_field::field_element_packed *__avx_dst[2];
prime_field::field_element* twiddle_factor;

void init_scratch_pad(int order)
{
    __dst[0] = new prime_field::field_element[order];//(prime_field::field_element*)malloc(order * sizeof(prime_field::field_element));
    __dst[1] = new prime_field::field_element[order];//(prime_field::field_element*)malloc(order * sizeof(prime_field::field_element));
    __dst[2] = new prime_field::field_element[order];
    __avx_dst[0] = new prime_field::field_element_packed[order / packed_size];
    __avx_dst[1] = new prime_field::field_element_packed[order / packed_size];
    twiddle_factor = new prime_field::field_element[order];
}

void delete_scratch_pad()
{
    delete[] __dst[0];
    delete[] __dst[1];
    delete[] __avx_dst[0];
    delete[] __avx_dst[1];
    delete[] twiddle_factor;
}

void fast_fourier_transform(const prime_field::field_element *coefficients, int coef_len, int order, prime_field::field_element root_of_unity, prime_field::field_element *result)
{
    prime_field::field_element rot_mul[62];
    //note: malloc and free will not call the constructor and destructor, not recommended unless for efficiency
    assert(sizeof(prime_field::field_element) * 2 == sizeof(__hhash_digest));
    //In sake of both memory and time efficiency, use the non-recursive version
    int lg_order = -1;
    rot_mul[0] = root_of_unity;
    for(int i = 0; i < 62; ++i)
    {
        if(i > 0)
            rot_mul[i] = rot_mul[i - 1] * rot_mul[i - 1];
        if((1LL << i) == order)
        {
            lg_order = i;
        }
    }
    int lg_coef = -1;
    for(int i = 0; i < 62; ++i)
    {
        if((1LL << i) == coef_len)
        {
            lg_coef = i;
        }
    }
    assert(lg_order != -1 && lg_coef != -1);
    assert(rot_mul[lg_order].real == 1 && rot_mul[lg_order].img == 0);

    //we can merge both cases, but I just don't want to do so since it's easy to make mistake
    if(lg_coef > lg_order)
    {
        assert(false);
    }
    else
    {
        //initialize leaves
        int blk_sz = (order / coef_len);
        for(int j = 0; j < blk_sz; ++j)
        {
            for(int i = 0; i < coef_len; ++i)
            {
                __dst[lg_coef & 1][(j << lg_coef) | i] = coefficients[i];
            }
        }

        prime_field::field_element *x_arr = new prime_field::field_element[1 << lg_order];

        {
            //initialize leaves
            int blk_sz = (order / coef_len);
            for(int j = 0; j < blk_sz; ++j)
            {
                for(int i = 0; i < coef_len / packed_size; ++i)
                {
                    __avx_dst[lg_coef & 1][((j << lg_coef) / packed_size) | i] = prime_field::field_element_packed(coefficients[i * packed_size], coefficients[i * packed_size + 1], coefficients[i * packed_size + 2], coefficients[i * packed_size + 3]);
                }
            }

            {
                for(int dep = lg_coef - 1; dep >= 0; --dep)
                {
                    int blk_size = 1 << (lg_order - dep);
                    int half_blk_size = blk_size >> 1;
                    int cur = dep & 1;
                    int pre = cur ^ 1;

                    prime_field::field_element x = prime_field::field_element(1);
                    prime_field::field_element_packed x_pack = prime_field::field_element_packed(prime_field::field_element(1), prime_field::field_element(1), prime_field::field_element(1), prime_field::field_element(1));
                    prime_field::field_element_packed x_multplier = prime_field::field_element_packed(rot_mul[dep], rot_mul[dep], rot_mul[dep], rot_mul[dep]);

                    if((1 << dep) >= packed_size)
                    {
                        for(int k = 0; k < blk_size / 2; ++k)
                        {
                            int double_k = (k) & (half_blk_size - 1);
                            for(int j = 0; j < (1 << dep) / (packed_size); ++j)
                            {
                                auto l_value = __avx_dst[pre][(double_k << (dep + 1)) / packed_size | j];
                                auto r_value = x_pack * __avx_dst[pre][(double_k << (dep + 1) | (1 << dep)) / packed_size | j];
                                __avx_dst[cur][(k << dep) / packed_size | j] = l_value + r_value;
                                __avx_dst[cur][((k + blk_size / 2) << dep) / packed_size | j] = l_value - r_value;
                            }
                            x_pack = x_pack * x_multplier;
                        }
                    }
                    else
                    {
                        //unrolling loop
                        prime_field::field_element sav[4];
                        if(dep == 1)
                        {
                            x_pack = prime_field::field_element_packed(prime_field::field_element(1), prime_field::field_element(1), rot_mul[dep], rot_mul[dep]);
                            x_multplier = prime_field::field_element_packed(rot_mul[dep] * rot_mul[dep], rot_mul[dep] * rot_mul[dep], rot_mul[dep] * rot_mul[dep], rot_mul[dep] * rot_mul[dep]);
                            for(int k = 0; k < blk_size / packed_size * 2; ++k)
                            {
                                int double_k_0 = (k << 1) & (half_blk_size - 1);
                                int double_k_1 = ((k << 1) | 1) & (half_blk_size - 1);
                                prime_field::field_element_packed double_k_0_pack = __avx_dst[pre][double_k_0], double_k_1_pack = __avx_dst[pre][double_k_1];
                                prime_field::field_element_packed odd_pack, even_pack;
                                odd_pack.img = _mm256_permute2x128_si256(double_k_0_pack.img, double_k_1_pack.img, 1 | (3 << 4));
                                odd_pack.real = _mm256_permute2x128_si256(double_k_0_pack.real, double_k_1_pack.real, 1 | (3 << 4));

                                even_pack.img = _mm256_permute2x128_si256(double_k_0_pack.img, double_k_1_pack.img, 0 | (2 << 4));
                                even_pack.real = _mm256_permute2x128_si256(double_k_0_pack.real, double_k_1_pack.real, 0 | (2 << 4));

                                __avx_dst[cur][k] = even_pack + x_pack * odd_pack;
                                __avx_dst[cur][k].get_field_element(sav);

                                for(int shift = 0; shift < 4; ++shift)
                                {
                                    __dst[cur][k * packed_size + shift] = sav[shift];
                                }
                                x_pack = x_pack * x_multplier;
                            }
                        }
                        else if(dep == 0)
                        {
                            x_arr[0] = prime_field::field_element(1);
                            for(int j = 1; j < blk_size; ++j)
                                x_arr[j] = x_arr[j - 1] * rot_mul[dep];
                            for(int k = 0; k < blk_size / 2; ++k)
                            {
                                int double_k = (k) & (half_blk_size - 1);
                                for(int j = 0; j < (1 << dep); ++j)
                                {
                                    auto l_value = __dst[pre][double_k << (dep + 1) | j], r_value = x_arr[k] * __dst[pre][double_k << (dep + 1) | (1 << dep) | j];
                                    __dst[cur][k << dep | j] = l_value + r_value;
                                    __dst[cur][(k + blk_size / 2) << dep | j] = l_value - r_value;
                                }
                            }
                        }
                    }
                }
            }
        }
        delete[] x_arr;
    }

    for(int i = 0; i < order; ++i)
        result[i] = __dst[0][i];
}

void inverse_fast_fourier_transform(prime_field::field_element *evaluations, int coef_len, int order, prime_field::field_element root_of_unity, prime_field::field_element *dst)
{
    if(coef_len > order)
    {
        //more coefficient than evaluation
        fprintf(stderr, "Warning, Request do inverse fft with inefficient number of evaluations.");
        fprintf(stderr, "Will construct a polynomial with less order than required.");
        coef_len = order;
    }

    //assume coef_len <= order

    //subsample evalutions

    prime_field::field_element *sub_eval;
    bool need_free = false;
    if(coef_len != order)
    {
        need_free = true;
        sub_eval = (prime_field::field_element*)malloc(coef_len * sizeof(prime_field::field_element));
        for(int i = 0; i < coef_len; ++i)
        {
            sub_eval[i] = evaluations[i * (order / coef_len)];
        }
    }
    else
        sub_eval = evaluations;

    prime_field::field_element new_rou = prime_field::field_element(1);
    for(int i = 0; i < order / coef_len; ++i)
        new_rou = new_rou * root_of_unity;
    order = coef_len;

    prime_field::field_element inv_rou = prime_field::field_element(1), tmp = new_rou;
    int lg_order = -1;
    for(int i = 0; i < 62; ++i)
    {
        if((1LL << i) == order)
        {
            lg_order = i;
        }
    }
    int lg_coef = -1;
    for(int i = 0; i < 62; ++i)
    {
        if((1LL << i) == coef_len)
        {
            lg_coef = i;
        }
    }
    assert(lg_order != -1 && lg_coef != -1);

    for(int i = 0; i < lg_order; ++i)
    {
        inv_rou = inv_rou * tmp;
        tmp = tmp * tmp;
    }
    assert(inv_rou * new_rou == prime_field::field_element(1));

    fast_fourier_transform(sub_eval, order, coef_len, inv_rou, dst);

    if(need_free)
        free(sub_eval);

    prime_field::field_element inv_n = fast_pow(prime_field::field_element(order), prime_field::mod - 2);
    assert(inv_n * prime_field::field_element(order) == prime_field::field_element(1));

    for(int i = 0; i < coef_len; ++i)
    {
        dst[i] = dst[i] * inv_n;
    }
}

// Warning: will change content in r
inline prime_field::field_element& _multi_by_minus_i(prime_field::field_element& r) {
    unsigned long long tmp = r.real;
    if (tmp == 0) tmp == prime_field::mod;
    r.real = r.img;
    r.img = prime_field::mod - tmp;
    return r;
}

inline prime_field::field_element& _multi_by_i(prime_field::field_element& r) {
    unsigned long long tmp = r.img;
    if (tmp == 0) tmp == prime_field::mod;
    r.img = r.real;
    r.real = prime_field::mod - tmp;
    return r;
}

void fast_fourier_transform_optim(const prime_field::field_element *coefficients, int coef_len, int order, prime_field::field_element root_of_unity, prime_field::field_element *result, bool inverse) {
    // for convenience, let coef_len == order for now
    assert(coef_len == order);
    int log_size = 31 - __builtin_clz(coef_len);

    int step, l_id, r_id, k_id, working_array_id = 0;
    int half_coef_len = coef_len >> 1, quarter_coef_len = coef_len >> 2;
    prime_field::field_element& (*func_quarter) (prime_field::field_element&);
    if (inverse) {
        func_quarter = _multi_by_i;
    } else {
        func_quarter = _multi_by_minus_i;
    }

    prime_field::field_element l_value, r_value, mult;
    prime_field::field_element *cur = __dst[working_array_id], *prev;

    twiddle_factor[0] = prime_field::field_element(1);
    for (int i = 1; i < coef_len; ++i) {
        twiddle_factor[i] = twiddle_factor[i-1] * root_of_unity;
    }

    // take this out, initialize size-2 fft w/o multi ops
    for (int i = 0; i < half_coef_len; ++i) {
        r_id = i + half_coef_len;
        l_value = coefficients[i];
        r_value = coefficients[r_id];
        cur[i] = l_value + r_value;
        cur[r_id] = l_value - r_value;
    }

    for (int i = 2; i <= log_size; ++i) {
        working_array_id = 1 ^ working_array_id;
        step = coef_len >> i;
        cur = __dst[working_array_id];
        prev = __dst[1 ^ working_array_id];

        // k = 0, multi by 1
        for (int offset = 0; offset < step; ++offset) {
            l_value = prev[offset];
            r_value = prev[offset + step];

            cur[offset] = l_value + r_value;
            cur[offset + half_coef_len] = l_value - r_value;
        }

        // k = N / 4, multi by -i or i, depends on fft or ifft
        for (int offset = 0; offset < step; ++offset) {
            l_id = offset + half_coef_len;
            k_id = offset + quarter_coef_len;

            l_value = prev[l_id];
            r_value = (*func_quarter)(prev[l_id + step]);

            cur[k_id] = l_value + r_value;
            cur[k_id + half_coef_len] = l_value - r_value;
        }

        // All others
        for (int k = step; k < half_coef_len; k += step) {
            if (k == quarter_coef_len) continue;
            mult = twiddle_factor[k];
            for (int offset = 0; offset < step; ++offset) {
                l_id = offset + (k << 1);
                k_id = offset + k;

                l_value = prev[l_id];
                r_value = prev[l_id + step] * mult;

                cur[k_id] = l_value + r_value;
                cur[k_id + half_coef_len] = l_value - r_value;
            }
        }

    }
    memcpy(result, __dst[working_array_id], sizeof(prime_field::field_element) * coef_len);
}

void inverse_fast_fourier_transform_optim(prime_field::field_element *evaluations, int coef_len, int order, prime_field::field_element root_of_unity, prime_field::field_element *dst) {
    assert(coef_len == order); // for now, for convenience...
    auto root_of_unity_inv = prime_field::inv(root_of_unity);
    fast_fourier_transform_optim(evaluations, coef_len, order, root_of_unity_inv, dst, true);
    prime_field::field_element inv_n = fast_pow(prime_field::field_element(order), prime_field::mod - 2);
    for(int i = 0; i < coef_len; ++i) {
        dst[i] = dst[i] * inv_n;
    }
}
