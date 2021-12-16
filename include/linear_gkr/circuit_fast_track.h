#ifndef __circuit
#define __circuit
#include <utility>
#include "linear_gkr/prime_field.h"
#include <unordered_map>
#include <vector>

class gate
{
public:
	int ty;
	long long u, v;
	gate(){}
	gate(int t, long long U, long long V)
	{
		ty = t, u = U, v = V;
	}
};

class layer
{
public:
	gate *gates;
	int bit_length;
	layer()
	{
		gates = NULL;
		bit_length = 0;
	}
	~layer()
	{
		delete[] gates;
	}
};

class layered_circuit
{
public:
	layer *circuit;
	int total_depth;
	prime_field::field_element *inputs;
	
	layered_circuit()
	{
		circuit = NULL;
		total_depth = 0;
		inputs = NULL;
	}
	~layered_circuit()
	{
		delete[] inputs;
		delete[] circuit;
	}
};

#endif
