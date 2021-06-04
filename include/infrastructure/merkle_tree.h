#ifndef __merkle_tree
#define __merkle_tree
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include <wmmintrin.h>
#include "my_hhash.h"
#include <utility>
#include <vector>

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
    std::pair<std::vector<__hhash_digest>, bool> verify_claim(__hhash_digest root_hhash, const __hhash_digest* tree, __hhash_digest leaf_element, int pos_element, int merkle_tree_size);
}
}

#endif