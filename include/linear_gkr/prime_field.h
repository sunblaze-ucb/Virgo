#pragma once
#ifndef __prime_field
#define __prime_field

//#include <boost/multiprecision/cpp_int.hpp>
//#include <boost/random.hpp>
#include <cassert>
#include <string>
#include <gmp.h>
#include <gmpxx.h>
#include <vector>

//using namespace boost::multiprecision;
//using namespace boost::random;

namespace prime_field
{
	class u256b
	{
	public:
		unsigned long long lo, mid;
		__uint128_t hi;
		u256b();
		u256b(const unsigned long long &x);
		u256b(const __uint128_t &x);

		u256b(const char* x, int len, int base);

		inline u256b operator + (const u256b &x) const;

		inline u256b operator - (const u256b &x) const;

		//inline u256b operator << (const int &x) const;
		//inline u256b operator >> (const int &x) const;


		u256b operator * (const u256b &x) const;
		
		inline u256b left_128();
		
		inline u256b operator & (const u256b &x) const;
		inline int bit_at(int pos) const;
		inline bool operator <= (const u256b &x) const;
		inline bool operator != (const u256b &x) const;

		inline bool operator > (const u256b &x) const;
		inline bool operator < (const u256b &x) const;
		int bitLen();
		int testBit(int i);
	};
	//extern int512_t mod;
	extern bool initialized;
	//extern independent_bits_engine<mt19937, 256, cpp_int> gen;
	
	extern u256b mod;

	class u512b
	{
	public:
		__uint128_t lo, mid;
		u256b hi;

		u512b(const u256b &x);
		u512b(const __uint128_t &x);
		u512b(const char* x, int len, int base);

		u512b();
		u512b operator + (const u512b &x) const;

		u512b operator - (const u512b &x) const;
		
		u512b operator * (const u512b &x) const;
		
		u512b operator % (const u256b &x) const;
		bool operator != (const u512b &x) const;
		bool operator > (const u512b &x) const;

		bool operator >= (const u512b &x) const;

		bool operator < (const u512b &x) const;
		void random();
	};
	extern u512b mod_512, minus_mod_512;

	void init(std::string, int);
	void init_random();
	/*
	This defines a prime field
	*/
	class field_element
	{
	private:
	public:
		u512b value;

		field_element();
		field_element(const int);
		field_element(const unsigned long long);
		field_element operator + (const field_element &b) const;
		field_element operator * (const field_element &b) const;
		field_element operator / (const field_element &b) const;
		field_element operator - (const field_element &b) const;
		bool operator == (const field_element &b) const;
		field_element mul_non_mod(const field_element &b) const;
		char* to_string();
		int bitLen();
		bool operator != (const field_element &b) const;
		mpz_class to_gmp_class();
		std::vector<bool> bit_stream();
	};
	field_element random();
    field_element fast_pow(field_element, long long);
    field_element inv(field_element);
    field_element get_root_of_unity(long long);
}
#endif