#pragma once

#include <vector>
#include <cstdio>
#include "linear_gkr/prime_field.h"
#include "infrastructure/my_hhash.h"
#include "infrastructure/merkle_tree.h"
class fiat_shamir
{
public:
    std::vector<char> transcript;
    std::vector<char> latest_update;
    __hhash_digest last_hash;
    fiat_shamir()
    {
        transcript.clear();
        latest_update.clear();
        memset(&last_hash, 0, sizeof(last_hash));
    }
    void randomize(int seed)
    {
        last_hash.data[0] = seed;
        last_hash.data[1] = seed >> 8;
        last_hash.data[2] = seed >> 16;
        last_hash.data[3] = seed >> 24;
        transcript.insert(transcript.end(), last_hash.data, last_hash.data + 4);
    }
    void push_latest_update()
    {
        transcript.insert(transcript.end(), latest_update.begin(), latest_update.end());
        latest_update.clear();
    }
    void output(const char *output_path)
    {
        push_latest_update();
        FILE *proof_file;
        proof_file = fopen(output_path, "wb");

        fwrite(transcript.data(),transcript.size(),1,proof_file);
        printf("Proof size %d bytes\n", transcript.size());
        fclose(proof_file);
    }

    void update(const char *data, int size)
    {
        latest_update.insert(latest_update.end(), data, data + size);
    }

    __hhash_digest get_hash()
    {
        std::vector<char> hash_data;
        if(latest_update.size() == 0)
        {
            return last_hash;
        }
        hash_data.insert(hash_data.end(), last_hash.data, last_hash.data + 256 / 8);
        hash_data.insert(hash_data.end(), latest_update.begin(), latest_update.end());

        sha256_update_shani((const unsigned char*)hash_data.data(), hash_data.size(), last_hash.data);
        return last_hash;
    }

    std::vector<prime_field::field_element> get_rand(int length)
    {
        get_hash();
        push_latest_update();
        std::vector<prime_field::field_element> ret;
        __hhash_digest current_hash = last_hash;
        __hhash_digest data[2];
        for(int i = 0; i < length; ++i)
        {
            ret.push_back(prime_field::from_hash(current_hash));
            data[0] = data[1] = current_hash;
            my_hhash(data, &current_hash);
        }
        return ret;
    }
};

prime_field::field_element get_unified_hash(fiat_shamir *verifiers, int N);