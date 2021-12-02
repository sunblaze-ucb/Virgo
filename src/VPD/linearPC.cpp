#include "infrastructure/merkle_tree.h"
#include "linear_code/linear_code_encode.h"
#include "linear_gkr/verifier.h"
#include "linear_gkr/prover.h"
#include <math.h>

//commit
prime_field::field_element **encoded_codeword;
prime_field::field_element **coef;
long long *codeword_size;
__hhash_digest *mt;
zk_prover p;
zk_verifier v;
__hhash_digest commit(const prime_field::field_element *src, int N)
{
    __hhash_digest *stash = new __hhash_digest[N / column_size * 2];
    codeword_size = new long long[column_size];
    assert(N % column_size == 0);
    encoded_codeword = new prime_field::field_element*[column_size];
    coef = new prime_field::field_element*[column_size];
    for(int i = 0; i < column_size; ++i)
    {
        encoded_codeword[i] = new prime_field::field_element[N / column_size * 2];
        coef[i] = new prime_field::field_element[N / column_size];
        memcpy(coef[i], &src[i * N / column_size], sizeof(prime_field::field_element) * N / column_size);
        memset(encoded_codeword[i], 0, sizeof(prime_field::field_element) * N / column_size * 2);
        codeword_size[i] = encode(&src[i * N / column_size], encoded_codeword[i], N / column_size);
    }

    for(int i = 0; i < N / column_size * 2; ++i)
    {
        memset(&stash[i], 0, sizeof(__hhash_digest));
        for(int j = 0; j < column_size / 2; ++j)
        {
            __hhash_digest data[2];
            data[0] = stash[i];
            prime_field::field_element element[2];
            element[0] = encoded_codeword[2 * j][i];
            element[1] = encoded_codeword[2 * j + 1][i];
            memcpy(&data[1], element, 2 * sizeof(prime_field::field_element));
            assert(2 * sizeof(prime_field::field_element) == sizeof(__hhash_digest));
            my_hhash(data, &stash[i]);
        }
    }

    merkle_tree::merkle_tree_prover::create_tree(stash, N / column_size * 2, mt, sizeof(__hhash_digest), true);
    return mt[0];
}

void generate_circuit(int* query, int N, int query_count, prime_field::field_element *input)
{
    assert((1LL << mylog(N)) == N);
    v.C.inputs = new prime_field::field_element[N];
    for(int i = 0; i < N; ++i)
    {
        v.C.inputs[i] = input[i];
        
    }
    for(int i = 0; i < N; ++i)
    {

    }
}

std::pair<prime_field::field_element, bool> tensor_product_protocol(prime_field::field_element *r0, prime_field::field_element *r1, int size_r0, int size_r1, int N)
{
    assert(size_r0 * size_r1 == N);

    int proof_size = 0;

    const int query_count = -128 / (log2(1 - target_distance));
    printf("Query count %d\n", query_count);

    //prover construct the combined codeword

    prime_field::field_element *combined_codeword = new prime_field::field_element[codeword_size[0]];
    memset(combined_codeword, 0, sizeof(prime_field::field_element) * codeword_size[0]);
    for(int i = 0; i < column_size; ++i)
    {
        for(int j = 0; j < codeword_size[0]; ++j)
        {
            combined_codeword[j] = combined_codeword[j] + r0[i] * encoded_codeword[i][j];
        }
    }
    
    //prover construct the combined original message
    prime_field::field_element *combined_message = new prime_field::field_element[N];
    memset(combined_message, 0, sizeof(prime_field::field_element) * N);
    for(int i = 0; i < column_size; ++i)
    {
        for(int j = 0; j < codeword_size[0]; ++j)
        {
            combined_message[j] = combined_message[j] + r0[i] * coef[i][j];
        }
    }

    //check for encode
    {
        prime_field::field_element *test_codeword = new prime_field::field_element[N / column_size * 2];
        int test_codeword_size = encode(combined_message, test_codeword, N / column_size);
        assert(test_codeword_size == codeword_size[0]);
        for(int i = 0; i < test_codeword_size; ++i)
        {
            assert(test_codeword[i] == combined_codeword[i]);
        }
    }

    //verifier random check columns
    for(int i = 0; i < query_count; ++i)
    {
        int q = rand() % codeword_size[0];
        prime_field::field_element sum = prime_field::field_element(0ULL);
        for(int j = 0; j < column_size; ++j)
        {
            sum = sum + r0[j] * encoded_codeword[q][j];
        }
        assert(sum == combined_codeword[q]);
    }

    //setup code-switching
    prime_field::field_element answer = prime_field::field_element(0ULL);
    for(int i = 0; i < N / column_size; ++i)
    {
        answer = answer + r1[i] * combined_message[i];
    }
    
    // prover commit private input

    // verifier samples query
    int *q = new int[query_count];
    for(int i = 0; i < query_count; ++i)
    {
        q[i] = rand() % codeword_size[0];
    }
    // generate circuit

    generate_circuit(q, N, query_count, combined_message);


    v.get_prover(&p);

    bool result = v.verify("log.txt");
    return std::make_pair(answer, result);
}

//open & verify

std::pair<prime_field::field_element, bool> open_and_verify(prime_field::field_element x, int N)
{
    assert(N % column_size == 0);
    //tensor product of r0 otimes r1
    prime_field::field_element *r0, *r1;
    r0 = new prime_field::field_element[column_size];
    r1 = new prime_field::field_element[N / column_size];

    prime_field::field_element x_n = prime_field::fast_pow(x, N / column_size);
    r0[0] = prime_field::field_element(1ULL);
    for(int j = 1; j < column_size; ++j)
    {
        r0[j] = r0[j - 1] * x_n;
    }
    r1[0] = prime_field::field_element(1ULL);
    for(int j = 1; j < N / column_size; ++j)
    {
        r1[j] = r1[j - 1] * x;
    }

    auto answer = tensor_product_protocol(r0, r1, column_size, N / column_size, N);

    delete[] r0;
    delete[] r1;
    return answer;
}

std::pair<prime_field::field_element, bool> open_and_verify(prime_field::field_element *r, int size_r, int N)
{
    assert(0);
}