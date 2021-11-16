#include "linear_gkr/prime_field.h"
#include <cmath>
#include <climits>
#include <ctime>
#include <iostream>
namespace prime_field
{

	const __uint128_t __max_ull = ULLONG_MAX;
	const __uint128_t __zero = 0LL;
	const __uint128_t __max_128 = ~(__zero);



	
	u256b::u256b(){lo = mid = 0; hi = 0;}
	u256b::u256b(const unsigned long long &x)
	{
		lo = x;
		mid = 0;
		hi = 0;
	}
	u256b::u256b(const __uint128_t &x)
	{
		lo = (unsigned long long)(x & __max_ull);
		mid = (unsigned long long)(x >> 64);
		hi = 0;
	}

	u256b::u256b(const char* x, int len, int base)
	{
		u256b ret = (u256b)(unsigned long long)0;
		u256b tmp = (u256b)(unsigned long long)1;
		for(int i = len - 1; i >= 0; --i)
		{
			ret = ret + tmp * ((u256b)(unsigned long long)(x[i] - '0'));
			tmp = tmp * ((u256b)(unsigned long long)base);
		}
		*this = ret;
	}

	inline u256b u256b::operator + (const u256b &x) const
	{
		u256b ret;
		bool carry;
		__uint128_t midd;
		ret.lo = lo + x.lo;
		carry = (ret.lo < lo);
		midd = (__uint128_t)mid + (__uint128_t)x.mid;
		if(midd == __max_ull)
			midd += carry;
		ret.mid = mid + x.mid + carry;
		ret.hi = hi + x.hi + (midd >> 64);
		return ret;
	}

	inline u256b u256b::operator - (const u256b &x) const
	{
		u256b not_x;
		not_x.lo = ~x.lo;
		not_x.mid = ~x.mid;
		not_x.hi = ~x.hi;
		return *this + not_x;
	}

	u256b u256b::operator * (const u256b &x) const
	{
		u256b ret;
		__uint128_t lolo = (__uint128_t)lo * (__uint128_t)x.lo;
		
		__uint128_t lomid1 = (__uint128_t)mid * (__uint128_t)x.lo;
		__uint128_t lomid2 = (__uint128_t)lo * (__uint128_t)x.mid;
		
		//hi * hi omitted
		ret.lo = (unsigned long long)lolo;
		__uint128_t carry = lolo >> 64; //this carry is less than 2**64
		ret.mid = ((unsigned long long)lomid1 + (unsigned long long)lomid2 + (unsigned long long)carry);
		//this carry is not necessary less than 2**64
		__uint128_t carry2 = ((lomid1 >> 64) + (lomid2 >> 64)) + 
						   (((lomid1 & __max_ull) + (lomid2 & __max_ull) + carry) >> 64);
						   
		ret.hi = (__uint128_t)lo * (__uint128_t)x.hi + (__uint128_t)hi * (__uint128_t)x.lo + 
				 (__uint128_t)mid * (__uint128_t)x.mid + (((__uint128_t)mid * (__uint128_t)x.hi + (__uint128_t)hi * (__uint128_t)x.mid) << 64) + carry2;
		return ret;
	}
	inline u256b u256b::left_128()
	{
		u256b ret;
		ret.lo = 0;
		ret.mid = 0;
		ret.hi = ((__uint128_t)lo | ((__uint128_t)mid << 64));
		return ret;
	}
	
	inline u256b u256b::operator & (const u256b &x) const
	{
		u256b ret;
		ret.lo = lo & x.lo;
		ret.mid = mid & x.mid;
		ret.hi = hi & x.hi;
		return ret;
	}
	inline int u256b::bit_at(int pos) const
	{
		if(pos < 64)
			return (lo >> pos) & 1;
		if(pos < 128)
			return (mid >> (pos - 64)) & 1;
		else
			return (hi >> (pos - 128)) & 1;
	}
	inline bool u256b::operator <= (const u256b &x) const
	{
		if(hi < x.hi)
			return true;
		if(hi > x.hi)
			return false;
		if(mid < x.mid)
			return true;
		if(mid > x.mid)
			return false;
		if(lo <= x.lo)
			return true;
		return false;
	}
	inline bool u256b::operator != (const u256b &x) const
	{
		return hi != x.hi || lo != x.lo || mid != x.mid;
	}

	inline bool u256b::operator > (const u256b &x) const
	{
		if(hi > x.hi)
			return true;
		if(hi < x.hi)
			return false;
		if(mid > x.mid)
			return true;
		if(mid < x.mid)
			return false;
		return lo > x.lo;
	}
	inline bool u256b::operator < (const u256b &x) const
	{
		if(hi < x.hi)
			return true;
		if(hi > x.hi)
			return false;
		if(mid < x.mid)
			return true;
		if(mid > x.mid)
			return false;
		return lo < x.lo;
	}

	inline u256b midhi_mul(const u256b &a, const u256b &b)
	{
		u256b ret;
		__uint128_t lolo = (__uint128_t)a.lo * (__uint128_t)b.lo;
		
		__uint128_t lomid1 = (__uint128_t)a.mid * (__uint128_t)b.lo;
		__uint128_t lomid2 = (__uint128_t)a.lo * (__uint128_t)b.mid;
		
		//hi * hi omitted
		ret.lo = (unsigned long long)lolo;
		__uint128_t carry = lolo >> 64; //this carry is less than 2**64
		ret.mid = ((unsigned long long)lomid1 + (unsigned long long)lomid2 + (unsigned long long)carry);				   
		return ret;
	}

	inline int u256b::bitLen()
	{
		if(hi != 0)
		{
			unsigned long long hihi, hilo;
			unsigned long long zero = 0;
			hihi = hi >> 64;
			hilo = hi & (~zero);
			if(hihi != 0)
				return 256 - __builtin_clzll(hihi);
			else
				return 256 - 64 - __builtin_clzll(hilo);
		}
		else if(mid != 0)
		{
			return 128 - __builtin_clzll(mid);
		}
		else
		{
			return 64 - __builtin_clzll(lo);
		}
	}

	int u256b::testBit(int i)
	{
		if(i <= 64)
		{
			return (lo >> i) & 1;
		}
		else if(i <= 128)
		{
			return (mid >> (i - 64)) & 1;
		}
		else
		{
			return (hi >> (i - 128)) & 1;
		}
	}

	u256b one, zero;

	u512b::u512b(const u256b &x)
	{
		lo = ((__uint128_t)x.mid << 64) | (__uint128_t)x.lo;
		mid = x.hi;
		hi.lo = 0;
		hi.mid = 0;
		hi.hi = 0;
	}
	u512b::u512b(const __uint128_t &x)
	{
		lo = x;
		mid = 0;
		hi.lo = 0;
		hi.mid = 0;
		hi.hi = 0;
	}
	u512b::u512b(const char* x, int len, int base)
	{
		u512b ret = (u256b)(unsigned long long)0;
		u512b tmp = (u256b)(unsigned long long)1;
		for(int i = len - 1; i >= 0; --i)
		{
			ret = ret + tmp * (u512b)((u256b)(unsigned long long)(x[i] - '0'));
			tmp = tmp * (u512b)((u256b)(unsigned long long)10);
		}
		*this = ret;
	}

	u512b::u512b(){lo = mid = 0; hi.lo = 0; hi.mid = 0; hi.hi = 0;}
	u512b u512b::operator + (const u512b &x) const
	{
		u512b ret;
		__uint128_t carry, carry2;
		ret.lo = lo + x.lo;
		carry = ret.lo < lo;
		ret.mid = mid + x.mid + carry;
		if(carry == 0)
			carry2 = ret.mid < mid;
		else
			carry2 = ret.mid <= mid;
		ret.hi = hi + x.hi + carry2;
		return ret;
	}

	u512b u512b::operator - (const u512b &x) const
	{
		u512b not_x;
		not_x.hi.hi = ~x.hi.hi;
		not_x.hi.mid = ~x.hi.mid;
		not_x.hi.lo = ~x.hi.lo;
		not_x.mid = ~x.mid;
		not_x.lo = ~x.lo;
		not_x = not_x + one;
		return *this + not_x;
	}

	inline void mul_no_hi(const u256b &a, const u256b &b, u256b &ret)
	{
		const __uint128_t lolo = (__uint128_t)a.lo * (__uint128_t)b.lo;
		
		const __uint128_t lomid1 = (__uint128_t)a.mid * (__uint128_t)b.lo;
		const __uint128_t lomid2 = (__uint128_t)a.lo * (__uint128_t)b.mid;
		
		//hi * hi omitted
		ret.lo = (unsigned long long)lolo;
		const __uint128_t carry = lolo >> 64; //this carry is less than 2**64
		ret.mid = ((unsigned long long)lomid1 + (unsigned long long)lomid2 + (unsigned long long)carry);
		//this carry is not necessary less than 2**64
		const __uint128_t carry2 = ((lomid1 >> 64) + (lomid2 >> 64)) + 
						   (((lomid1 & __max_ull) + (lomid2 & __max_ull) + carry) >> 64);
						   
		ret.hi = (__uint128_t)a.mid * (__uint128_t)b.mid + carry2;
	}
	inline u512b u512b::operator * (const u512b &x) const
	{
		if(x.mid == 0 && x.lo == 0)
			return x;
		if(mid == 0 && lo == 0)
			return *this;
		u512b ret;
		const u256b alo = (u256b)lo, xlo = (u256b)x.lo;
		const u256b amid = (u256b)mid, xmid = (u256b)x.mid;
		u256b lolo; mul_no_hi(alo, xlo, lolo);
		
		u256b lomid1; mul_no_hi(amid, xlo, lomid1);
		u256b lomid2; mul_no_hi(alo, xmid, lomid2);

		u256b midmid; mul_no_hi(amid, xmid, midmid);
		
		
		//hi * hi omitted
		ret.lo = (__uint128_t)lolo.lo | ((__uint128_t)lolo.mid << 64);
		const __uint128_t carry = lolo.hi; //this carry is less than 2**128
		
		const u256b tmp = (lomid1 + lomid2 + carry);
		
		ret.mid = (__uint128_t)tmp.lo | ((__uint128_t)tmp.mid << 64);
		//this carry is not necessary less than 2**128
		//double sum = (double)lomid1.hi + (double)lomid2.hi + (double)lomid1.lo + (double)((__uint128_t)lomid1.mid << 64) + (double)lomid2.lo + (double)((__uint128_t)lomid2.mid << 64) + (double)carry;
		//sum = sum / max_int128;
		const u256b carry2 = ((u256b)(lomid1.hi) + (u256b)(lomid2.hi)) + 
						   (((u256b)((__uint128_t)lomid1.lo | ((__uint128_t)lomid1.mid << 64))
						   + (u256b)((__uint128_t)lomid2.lo | ((__uint128_t)lomid2.mid << 64)) + (u256b)carry).hi);
		
		//const u256b carry2 = (unsigned long long)(sum);

		//ret.hi = lohi1 + lohi2 + midmid + ((midhi1 + midhi2).left_128()) + carry2;
		ret.hi = midmid + carry2;
		return ret;
	}
	u256b my_factor;
	
//https://www.nayuki.io/page/barrett-reduction-algorithm
	u512b u512b::operator % (const u256b &x) const
	{
		if(lo == 0 && mid == 0 && hi.lo == 0 && hi.mid == 0 && hi.hi == 0)
			return *this;
		u512b hi_factor = (u512b)hi * (u512b)my_factor;
		u512b lo256bit;
		lo256bit.hi = (unsigned long long)0;
		lo256bit.mid = mid;
		lo256bit.lo = lo;
		const u512b lo_factor = (u512b)lo256bit * (u512b)my_factor;
		const u512b res = hi_factor + (u512b)lo_factor.hi;
		u256b t;
		t.hi = res.hi.hi << 4 | (res.hi.mid >> 60);
		t.mid = res.hi.mid << 4 | (res.hi.lo >> 60);
		t.lo = (res.hi.lo << 4) | (res.mid >> 124);
		u512b t512 = (u512b)t;
		t512 = *this - t512 * mod;

		auto result = t512;
		if(t512 >= mod)
			result = t512 - mod;
		return result;
	}
	bool u512b::operator != (const u512b &x) const
	{
		return lo != x.lo || mid != x.mid || hi != x.hi;
	}
	bool u512b::operator > (const u512b &x) const
	{
		if(hi > x.hi)
			return true;
		if(hi < x.hi)
			return false;
		if(mid > x.mid)
			return true;
		if(mid < x.mid)
			return false;
		return lo > x.lo;
	}

	bool u512b::operator >= (const u512b &x) const
	{
		if(hi > x.hi)
			return true;
		if(hi < x.hi)
			return false;
		if(mid > x.mid)
			return true;
		if(mid < x.mid)
			return false;
		return lo >= x.lo;
	}

	bool u512b::operator < (const u512b &x) const
	{
		if(hi < x.hi)
			return true;
		if(hi > x.hi)
			return false;
		if(mid < x.mid)
			return true;
		if(mid > x.mid)
			return false;
		return lo < x.lo;
	}
	void u512b::random()
	{
		lo = rand();
		mid = rand();
		hi = (u256b)(unsigned long long)rand();
	}



	u256b mod;
	u512b minus_mod_512, mod_512;
	const int shift = 508;
	bool initialized = false;
    field_element root_of_unity;
    const int max_order = 28;

	void init(std::string s, int base)
	{
		assert(base == 10);
		initialized = true;
		mod = u256b(s.c_str(), s.length(), base);
		one = (u256b)(unsigned long long)1;
		zero = (u256b)(unsigned long long)0;

		std::string factor_s = "38284845454613504619394467267190322316714506535725634610690744705837986343205";
		my_factor = u256b(factor_s.c_str(), factor_s.length(), 10);
		minus_mod_512 = prime_field::field_element(0).value - mod;
		mod_512 = mod;

        std::string base_root_of_unity = "6506949774839052718110406215085119770091102268120408611511048664532142289545";
        root_of_unity.value = u256b(base_root_of_unity.c_str(), base_root_of_unity.length(), 10);
	}
	void init_random()
	{
	}
	field_element::field_element()
	{
		value = (u256b)(unsigned long long)0;
	}
	field_element::field_element(const int x)
	{
		value = (u256b)(unsigned long long)x;
	}
	field_element::field_element(const unsigned long long x)
	{
		value = (u256b)(unsigned long long)x;
	}
	field_element field_element::operator + (const field_element &b) const
	{
		field_element ret;
		ret.value = (b.value + value);
		if(ret.value >= mod_512)
			ret.value = ret.value + minus_mod_512;
		return ret;
	}
	field_element field_element::mul_non_mod(const field_element &b) const
	{
		field_element ret;
		ret.value = (b.value * value);
		return ret;
	}
	field_element field_element::operator * (const field_element &b) const
	{
		field_element ret;
		ret.value = (b.value * value) % mod;
		return ret;
	}
	field_element field_element::operator / (const field_element &b) const
	{
		//todo
		assert(false);
		//return ret;
	}
	field_element field_element::operator - (const field_element &b) const
	{
		field_element ret;
		if(value >= b.value)
			ret.value = value - b.value;
		else
			ret.value = value + mod_512 - b.value;
		return ret;
	}
	char* field_element::to_string()
	{
		static char ret[512];
		for(int i = 0; i < 128; ++i)
			ret[i] = ((value.lo >> i) & 1) + '0';
		for(int i = 0; i < 128; ++i)
			ret[i + 128] = ((value.mid >> i) & 1) + '0';
		for(int i = 0; i < 256; ++i)
			ret[i + 256] = ((value.hi.bit_at(i)) & 1) + '0';
		return ret;
	}
	field_element random()
	{
		field_element ret;
		ret.value.random();
		ret.value = ret.value % mod;
		return ret;
	}
	bool field_element::operator != (const field_element &b) const
	{
		return value != b.value;
	}
	int field_element::bitLen()
	{
		if(value.hi != u256b((unsigned long long)0))
		{
			return value.hi.bitLen() + 256;
		}
		else if(value.mid != 0)
		{
			unsigned long long hi, lo;
			unsigned long long zero = 0;
			hi = value.mid >> 64;
			lo = value.mid & (~zero);
			if(hi != 0)
				return 256 - __builtin_clzll(hi);
			return 256 - 64 - __builtin_clzll(lo);
		}
		else
		{
			unsigned long long hi, lo;
			unsigned long long zero = 0;
			hi = value.lo >> 64;
			lo = value.lo & (~zero);
			if(hi != 0)
				return 128 - __builtin_clzll(hi);
			return 64 - __builtin_clzll(lo);
		}
	}
	mpz_class field_element::to_gmp_class()
	{
		char* str_value;
		str_value = new char[257];
		if(value.hi != u256b((unsigned long long)0))
			assert(false);
		for(int i = 0; i < 128; ++i)
			str_value[i] = ((value.lo >> i) & 1) + '0';
		for(int i = 0; i < 128; ++i)
			str_value[i + 128] = ((value.mid >> i) & 1) + '0';
		for(int i = 0; i < 128; ++i)
		{
			char x;
			x = str_value[i];
			str_value[i] = str_value[255 - i];
			str_value[255 - i] = x;
		}
		str_value[256] = 0;
		mpz_class ret(str_value, 2);
		delete str_value;
		return ret;
	} 
	bool field_element::operator == (const field_element &b) const
	{
		return !(*this != b);
	}
	std::vector<bool> field_element::bit_stream()
	{
		std::vector<bool> out;
		for(int i = 0; i < 128; ++i)
		{
			out.push_back((value.lo >> i) & 1);
		}
		
		for(int i = 0; i < 128; ++i)
		{
			out.push_back((value.mid >> i) & 1);
		}
		return out;
	}
    field_element fast_pow(field_element base, long long exp)
    {
        field_element ret;
        ret.value = (u256b)(unsigned long long)1;
        field_element tmp = base;
        while (exp)
        {
            if (exp & 1)
                ret = ret * tmp;
            exp >>= 1;
            tmp = tmp * tmp;
        }
        return ret;
        
    }
    field_element inv(field_element x)
    {
        const bool mod_minus_2_bits[] = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1};
        field_element ret;
        ret.value = (u256b)(unsigned long long)1;
        field_element tmp = x;
        for(int i = 0; i < 254; ++i)
        {
            if(mod_minus_2_bits[i])
            {
                ret = ret * tmp;
            }
            tmp = tmp * tmp;
        }
        return ret;
    }
    field_element get_root_of_unity(long long log_order)
    {
        field_element ret = root_of_unity;

        for(int i = 0; i < (max_order - log_order); ++i)
        {
            ret = ret * ret;
        }
		field_element tmp = ret;
		for(int i = 0; i < log_order; ++i)
		{
			tmp = tmp * tmp;
		}
		assert(tmp == prime_field::field_element(1));
        return ret;
    }
}