#ifndef __hhash
#define __hhash

/**extra 'h' before hhash can avoid some strange error by the compiler*/

#include <immintrin.h>
#include <wmmintrin.h>
#include <cassert>
#include "flo-shani-aesni/sha256/flo-shani.h"

class __hhash_digest
{
public:
    unsigned char data[256 / 8];
};

inline bool equals(const __hhash_digest &a, const __hhash_digest &b)
{
    bool result = true;
    for(int i = 0; i < 256 / 8; ++i)
    {
        result &= (a.data[i] == b.data[i]);
    }
    return result;
}

inline void my_hhash(const void* src, void* dst)
{
    sha256_update_shani((const unsigned char*)src, 64, (unsigned char*)dst);
}

#endif
