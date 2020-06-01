#ifndef __merkle_tree
#define __merkle_tree
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include <wmmintrin.h>
#include "my_hhash.h"

namespace merkle_tree
{
extern int size_after_padding;
namespace merkle_tree_prover
{
    //Merkle tree functions used by the prover
    //void create_tree(void* data_source_array, int lengh, void* &target_tree_array, const int single_element_size = 256/8)
    void create_tree(void* data, int ele_num, __hhash_digest* &dst, const int element_size, bool alloc_required);
}

namespace merkle_tree_verifier
{
    //Merkle tree functions used by the verifier
    bool verify_claim(__m128i root_hhash, const void* tree, __m128i hhash_element, int pos_element);
}
}

#endif