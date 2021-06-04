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
	std::unordered_map<int, std::vector<std::pair<int, std::pair<int, int> > > > u_gates;
	std::unordered_map<int, std::vector<std::pair<int, std::pair<int, int> > > > v_gates;
	bool is_parallel;
	int block_size;
	int log_block_size;
	int repeat_num;
	int log_repeat_num;
	bool is_all_direct_relay;
	layer()
	{
		is_all_direct_relay = false;
		is_parallel = false;
		gates = NULL;
		bit_length = 0;
	}
	~layer()
	{
	}
};

class layered_circuit
{
public:
	layer *circuit;
	int total_depth;
	layered_circuit()
	{
		circuit = NULL;
		total_depth = 0;
	}
	~layered_circuit()
	{
	}
};

#endif
