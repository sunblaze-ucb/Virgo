#ifndef __hhash
#define __hhash

/**extra 'h' before hhash can avoid some strange error by the compiler*/

#include <immintrin.h>
#include <wmmintrin.h>
#include <cassert>

class __hhash_digest
{
public:
    __m128i h0, h1;
};

inline bool equals(const __hhash_digest &a, const __hhash_digest &b)
{
    __m128i v0 = _mm_xor_si128(a.h0, b.h0);
    __m128i v1 = _mm_xor_si128(a.h1, b.h1);
    return _mm_test_all_zeros(v0, v0) && _mm_test_all_zeros(v1, v1);
}

inline void* hhash_4_para(void* src)
{
#ifdef AVX512
    
#else
    assert(false);
#endif
}

inline __m128i aes128_sec_extend(__m128i secret, const int rcon_index)
{
//    const static int 常数[] = {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36};
    __m128i tmp_secret;
    switch (rcon_index)
    {
        case 0:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x01);
            break;
        case 1:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x02);
            break;
        case 2:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x04);
            break;
        case 3:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x08);
            break;
        case 4:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x10);
            break;
        case 5:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x20);
            break;
        case 6:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x40);
            break;
        case 7:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x80);
            break;
        case 8:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x1B);
            break;
        case 9:
            tmp_secret = _mm_aeskeygenassist_si128(secret, 0x36);
            break;
        default:
            tmp_secret = secret;
            assert(false);
            break;
    }
    tmp_secret = _mm_shuffle_epi32(tmp_secret, _MM_SHUFFLE(3, 3, 3, 3));
    for(int i = 0; i < 3; ++i)
    {
        secret = _mm_xor_si128(secret, _mm_slli_si128(secret, 4));
    }
    return _mm_xor_si128(secret, tmp_secret);
}

inline __m128i aes128_enc(__m128i plain, __m128i secret)
{
    plain = _mm_xor_si128(plain, secret);
    for(int i = 0; i < 9; ++i)
    {
        secret = aes128_sec_extend(secret, i);
        plain = _mm_aesenc_si128(plain, secret);
    }
    secret = aes128_sec_extend(secret, 9);
    plain = _mm_aesenclast_si128(plain, secret);

    return plain;
}

//inline void* hhash(void* source)
inline void my_hhash(const void* src, void* dst)
{
    //从源数据中读取16bytes作为key
    /**read 16bytes from source data as key*/
    const __m128i key0 = _mm_loadu_si128((__m128i*)src);
    //从源数据中读取16bytes作为加密原文
    /**read 16bytes from source data as text*/
    const __m128i text0 = _mm_loadu_si128(((__m128i*)src) + 1);
   _mm_storeu_si128((__m128i*)dst, _mm_xor_si128(aes128_enc(text0, key0), text0));

    //从源数据中读取16bytes作为key
    /**read 16bytes from source data as key*/
    const __m128i key1 = _mm_loadu_si128((__m128i*)src + 2);
    //从源数据中读取16bytes作为加密原文
    /**read 16bytes from source data as text*/
    const __m128i text1 = _mm_loadu_si128(((__m128i*)src + 2) + 1);
   _mm_storeu_si128((__m128i*)dst + 1, _mm_xor_si128(aes128_enc(text1, key1), text1));
}

#endif