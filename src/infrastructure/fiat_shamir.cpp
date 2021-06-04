
#include "infrastructure/fiat_shamir.h"

prime_field::field_element get_unified_hash(fiat_shamir *verifiers, int N)
{
    __hhash_digest *merkle_data = new __hhash_digest[N];
    for(int i = 0; i < N; ++i)
    {
        __hhash_digest hash = verifiers[i].get_hash();
        merkle_data[i] = hash;
    }
    __hhash_digest *dst;
    merkle_tree::merkle_tree_prover::create_tree(merkle_data, N, dst, 256 / 8, true);
    __hhash_digest unified_hash = dst[1];

    for(int i = 0; i < N; ++i)
    {
        auto path = merkle_tree::merkle_tree_verifier::verify_claim(unified_hash, dst, merkle_data[i], i, N);
        assert(path.second);
        for(int j = 0; j < path.first.size(); ++j)
        {
            verifiers[i].latest_update.insert(verifiers[i].latest_update.end(), path.first[j].data, path.first[j].data + 256 / 8);
        }
        verifiers[i].push_latest_update();
        verifiers[i].last_hash = unified_hash;
    }
    return prime_field::from_hash(unified_hash);
}