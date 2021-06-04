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


std::pair<std::vector<__hhash_digest>, bool> merkle_tree::merkle_tree_verifier::verify_claim(__hhash_digest root_hhash, const __hhash_digest* tree, __hhash_digest leaf_element, int pos_element, int merkle_tree_size)
{
    std::vector<__hhash_digest> hash_path;
    __hhash_digest data[2];
    int leaf_addr = pos_element + merkle_tree_size;
    bool result = true;
    while(leaf_addr != 1)
    {
        if((leaf_addr & 1) == 1)
		{
			data[0] = tree[leaf_addr ^ 1];
			data[1] = leaf_element;
		}
        else
        {
            data[0] = leaf_element;
            data[1] = tree[leaf_addr ^ 1];
        }
        hash_path.push_back(tree[leaf_addr ^ 1]);
        my_hhash(data, &leaf_element);
        leaf_addr /= 2;
        result &= equals(leaf_element, tree[leaf_addr]);
        assert(result);
    }
    return std::make_pair(hash_path, result);
}