#include "linear_gkr/prime_field.h"
#include "infrastructure/merkle_tree.h"
int merkle_tree::size_after_padding;
void merkle_tree::merkle_tree_prover::create_tree(void* src_data, int ele_num, __hhash_digest* &dst, const int element_size = 256 / 8, bool alloc_required = false)
{
    assert(element_size == sizeof(prime_field::field_element) * 2);
    size_after_padding = 1;
    while(size_after_padding < ele_num)
        size_after_padding *= 2;

    __hhash_digest *dst_ptr;
    if(alloc_required)
    {
        dst_ptr = (__hhash_digest*)malloc(size_after_padding * 2 * element_size);
        if(dst_ptr == NULL)
        {
            printf("Merkle Tree Bad Alloc\n");
            abort();
        }
    }
    else
        dst_ptr = dst;
    //线段树要两倍大小
    dst = dst_ptr;
    memset(dst_ptr, 0, size_after_padding * 2 * element_size);

    int start_ptr = size_after_padding;
    int current_lvl_size = size_after_padding;
    __hhash_digest data[2];
    memset(data, 0, sizeof data);
    for(int i = current_lvl_size - 1; i >= 0; --i)
    {
        
        if(i < ele_num)
        {
            dst_ptr[i + start_ptr] = ((__hhash_digest*)src_data)[i];
        }
        else
        {
            memset(data, 0, sizeof data);
            my_hhash(data, &dst_ptr[i + start_ptr]);
        }
    }
    current_lvl_size /= 2;
    start_ptr -= current_lvl_size;
    while(current_lvl_size >= 1)
    {
        for(int i = 0; i < current_lvl_size; ++i)
        {
            data[0] = dst_ptr[start_ptr + current_lvl_size + i * 2];
            data[1] = dst_ptr[start_ptr + current_lvl_size + i * 2 + 1];
            my_hhash(data, &dst_ptr[start_ptr + i]);
        }
        current_lvl_size /= 2;
        start_ptr -= current_lvl_size;
    }
}

bool merkle_tree::merkle_tree_verifier::verify_claim(__m128i root_hhash, const void* tree, __m128i hhash_element, int pos_element_arr)
{
    int pos_element = pos_element_arr + size_after_padding;
    __m128i data[2];
    while(pos_element != 1)
    {
        data[pos_element & 1] = hhash_element;
        data[(pos_element & 1) ^ 1] = ((__m128i*)tree)[pos_element ^ 1];
        my_hhash(data, &hhash_element);
        pos_element /= 2;
    }
    long long *root_hhash_ptr = (long long*)&root_hhash;
    long long *answer_hhash_ptr = (long long*)&hhash_element;
    return root_hhash_ptr[0] == answer_hhash_ptr[0] && root_hhash_ptr[1] == answer_hhash_ptr[1];
}