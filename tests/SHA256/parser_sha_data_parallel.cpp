#include <cstdio>
#include <string>
#include <iostream>
#include <fstream>
#include <regex>
#include <map>
#include <vector>
#include <queue>
#include <cassert>
#include <algorithm>
using namespace std;

char source_gate0[1000], source_gate1[1000];
string source_line;
int target_gate, tgt;
long long src0, src1;
vector<int> input_gates;

regex add_gate("P V[0-9]+ = V[0-9]+ \\+ V[0-9]+ E");
regex mult_gate("P V[0-9]+ = V[0-9]+ \\* V[0-9]+ E");
regex constant_assign_gate("P V[0-9]+ = [\\-]*[0-9]+ E");
regex input_gate("P V[0-9]+ = I[0-9]+ E");
regex output_gate("P O[0-9]+ = V[0-9]+ E");
regex pass_gate("P V[0-9]+ = V[0-9]+ PASS V[0-9]+ E");
regex xor_gate("P V[0-9]+ = V[0-9]+ XOR V[0-9]+ E");
regex minus_gate("P V[0-9]+ = V[0-9]+ minus V[0-9]+ E");
regex naab_gate("P V[0-9]+ = V[0-9]+ NAAB V[0-9]+ E");
regex not_gate("P V[0-9]+ = V[0-9]+ NOT V[0-9]+ E");
regex exp_sum_gate("P V[0-9]+ = V[0-9]+ EXPSUM V[0-9]+ E");
regex bit_test_gate("P V[0-9]+ = V[0-9]+ BIT V[0-9]+ E");

smatch base_match;
int repeat_num;

enum gate_types
{
    add = 0,
    mult = 1,
    dummy = 2,
    input = 3,
    not_gate_id = 6, 
    minus_gate_id = 7,
    xor_gate_id = 8,
    naab_gate_id = 9,
    output_gate_id = 11,
    relay_gate_id = 10,
	exp_sum_gate_id = 12,
	bit_test_gate_id = 13
};

class gate
{
public:
	gate_types ty;
	int g;
	long long u, v;
	gate(){}
	gate(gate_types TY, int G, int U, int V)
	{
		ty = TY;
		g = G;
		u = U;
		v = V;
	}
};

class layer
{
public:
	vector<gate> gates;
	int bit_len;
	bool is_parallel;
	int block_size;
	int log_block_size;
};

class layered_circuit
{
public:
	vector<layer> layers;
	int depth;
};

class DAG_gate
{
public:
	pair<int, long long> input0, input1, id;
	int layered_id;
	int layered_lvl;
	bool is_output;
	gate_types ty;
	vector<pair<int, long long> > outputs;
};

class DAG_circuit
{
public:
	map<pair<int, long long>, DAG_gate> circuit;
};

layered_circuit rdl, sha256, sha256_combined;
DAG_circuit sha256_dag, sha256_dag_copy;

int relay_counter = 0;

void add_relay(pair<int, long long> id0, pair<int, long long> id1, int left_or_right)
{
	DAG_gate &g0 = sha256_dag_copy.circuit[id0];
	DAG_gate &g1 = sha256_dag_copy.circuit[id1];
	if(g0.layered_lvl == g1.layered_lvl + 1)
		return;
	else
	{
		auto pre_id = g1.id;
		for(int i = g1.layered_lvl + 1; i < g0.layered_lvl; ++i)
		{
			DAG_gate g;
			g.id = make_pair((int)'R', relay_counter++);
			g.layered_lvl = i;
			g.is_output = false;
			g.ty = relay_gate_id;
			g.input0 = pre_id;
			g.input1 = make_pair('N', 0);
			sha256_dag.circuit[g.id] = g;
			pre_id = g.id;
		}
		if(left_or_right == 0)
		{
			sha256_dag.circuit[g0.id].input0 = pre_id;	
		}
		else
		{
			sha256_dag.circuit[g0.id].input1 = pre_id;
		}
	}
}

vector<int> padding_num;

void DAG_to_layered()
{
	vector<int> layer_gate_count;
	map<pair<int, long long>, int> in_deg;
	for(auto x = sha256_dag.circuit.begin(); x != sha256_dag.circuit.end(); ++x)
	{
		auto &id = x -> first;
		auto &g = x -> second;
		for(auto y : g.outputs)
		{
			in_deg[y]++;
		}
		g.layered_lvl = -1;
	}
	queue<pair<int, long long> > q;
	for(auto x = sha256_dag.circuit.begin(); x != sha256_dag.circuit.end(); ++x)
	{
		auto &id = x -> first;
		if(in_deg[id] == 0)
		{
			assert((x -> second).ty == input);
		}
		(x -> second).layered_lvl = 0;
		q.push(id);
	}
	int max_lvl = -1;
	while(!q.empty())
	{
		auto cur = q.front();
		q.pop();
		auto &g = sha256_dag.circuit[cur];
		max_lvl = max(max_lvl, g.layered_lvl);
		for(auto x : g.outputs)
		{
			in_deg[x]--;
			sha256_dag.circuit[x].layered_lvl = max(sha256_dag.circuit[x].layered_lvl, g.layered_lvl + 1);
			if(in_deg[x] == 0)
			{
				q.push(x);
			}
		}
	}
	//relay gates
	sha256_dag_copy = sha256_dag;
	for(auto x = sha256_dag_copy.circuit.begin(); x != sha256_dag_copy.circuit.end(); ++x)
	{
		auto &id = x -> first;
		auto &g = x -> second;
		switch(g.ty)
		{
			case add:
			{
				auto input0 = g.input0;
				auto input1 = g.input1;
				add_relay(id, input0, 0);
				add_relay(id, input1, 1);
				break;
			}
			case mult:
			{
				auto input0 = g.input0;
				auto input1 = g.input1;
				add_relay(id, input0, 0);
				add_relay(id, input1, 1);
				break;
			}
			case input:
			{
				assert(g.layered_lvl == 0);
				break;
			}
			case not_gate_id:
			{
				auto input0 = g.input0;
				add_relay(id, input0, 0);
				break;
			}
			case minus_gate_id:
			{
				auto input0 = g.input0;
				auto input1 = g.input1;
				add_relay(id, input0, 0);
				add_relay(id, input1, 1);
				break;
			}
			case xor_gate_id:
			{
				auto input0 = g.input0;
				auto input1 = g.input1;
				add_relay(id, input0, 0);
				add_relay(id, input1, 1);
				break;
			}
			case naab_gate_id:
			{
				auto input0 = g.input0;
				auto input1 = g.input1;
				add_relay(id, input0, 0);
				add_relay(id, input1, 1);
				break;
			}
			case output_gate_id:
			{
				auto input0 = g.input0;
				add_relay(id, input0, 0);
				break;
			}
			case exp_sum_gate_id:
			{
				auto input0 = g.input0;
				auto input1 = g.input1;
				for(int i = input0.second; i <= input1.second; ++i)
				{
					auto &g0 = sha256_dag_copy.circuit[make_pair((int)'V', i)];
					assert(g0.layered_lvl + 1 == g.layered_lvl);
				}
				break;
			}
			case bit_test_gate_id:
			{
				auto input0 = g.input0;
				assert(g.input0 == g.input1);
				add_relay(id, input0, 0);
				break;
			}
		}
	}
	layer_gate_count.resize(max_lvl + 1);
	padding_num.resize(max_lvl + 1);
	for(int i = 0; i <= max_lvl; ++i)
		layer_gate_count[i] = 0, padding_num[i] = 0;
	for(auto x = sha256_dag.circuit.begin(); x != sha256_dag.circuit.end(); ++x)
	{
		auto &id = x -> first;
		auto &g = x -> second;
		layer_gate_count[g.layered_lvl]++;
	}
	
	sha256.depth = max_lvl + 1;
	sha256.layers.resize(sha256.depth);
	for(int i = 0; i <= max_lvl; ++i)
	{
		int lgc = layer_gate_count[i];
		int full_layer_count = 1;
		int bit_length = 0;
		while(lgc)
		{
			full_layer_count *= 2;
			lgc /= 2;
			bit_length++;
		}
		padding_num[i] = full_layer_count - layer_gate_count[i];
		if(padding_num[i] == 0)
			bit_length--;
		sha256.layers[i].bit_len = bit_length;
	}
	
	vector<int> layer_counter;
	layer_counter.resize(max_lvl + 1);
	for(int i = 0; i <= max_lvl; ++i)
	{
		layer_counter[i] = 0;
	}
	for(auto x = sha256_dag.circuit.begin(); x != sha256_dag.circuit.end(); ++x)
	{
		auto &id = x -> first;
		auto &g = x -> second;
		g.layered_id = layer_counter[g.layered_lvl]++;
	}
	
	sha256_dag_copy = sha256_dag;
	
	for(auto x = sha256_dag.circuit.begin(); x != sha256_dag.circuit.end(); ++x)
	{
		auto &id = x -> first;
		auto &g = x -> second;
		int lvl = g.layered_lvl;
		gate layer_gate;
		layer_gate.g = g.layered_id;
		layer_gate.ty = g.ty;
		layer_gate.u = sha256_dag_copy.circuit[g.input0].layered_id;
		layer_gate.v = sha256_dag_copy.circuit[g.input1].layered_id;
		if(g.ty == input || g.ty == relay_gate_id || g.ty == not_gate_id)
		{
			layer_gate.v = 0;
		}
		sha256.layers[lvl].gates.push_back(layer_gate);
		assert(sha256_dag_copy.circuit[g.input0].layered_lvl + 1 == lvl || g.ty == input);
		assert(sha256_dag_copy.circuit[g.input1].layered_lvl + 1 == lvl || g.ty == relay_gate_id || g.ty == not_gate_id || g.ty == input);
	}
	
	//padding
	for(int i = 0; i <= max_lvl; ++i)
	{
		for(int j = 0; j < padding_num[i]; ++j)
		{
			gate layer_gate;
			layer_gate.ty = dummy;
			layer_gate.u = layer_gate.v = 0;
			layer_gate.g = layer_counter[i]++;
			sha256.layers[i].gates.push_back(layer_gate);
		}
	}
}

int input_count = 0;

void read_circuit(ifstream &circuit_in)
{
	while(getline(circuit_in, source_line))
    {
        if(std::regex_match(source_line, base_match, add_gate))
        {
            sscanf(source_line.c_str(), "P V%d = V%lld + V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = add;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
        }
        else if(std::regex_match(source_line, base_match, mult_gate))
        {
            sscanf(source_line.c_str(), "P V%d = V%lld * V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = mult;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
        }
        else if(std::regex_match(source_line, base_match, constant_assign_gate))
		{
			assert(false);
            sscanf(source_line.c_str(), "P V%d = %lld E", &tgt, &src0);
		}
        else if(std::regex_match(source_line, base_match, input_gate))
        {
            sscanf(source_line.c_str(), "P V%d = I%lld E", &tgt, &src0);
            DAG_gate g;
            g.is_output = false;
            input_count++;
            g.ty = input;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'I', (int)src0);
            g.input1 = make_pair((int)'N', 0);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
        }
        else if(std::regex_match(source_line, base_match, output_gate))
        {
            sscanf(source_line.c_str(), "P O%d = V%lld E", &tgt, &src0);
            sha256_dag.circuit[make_pair((int)'V', (int)src0)].is_output = true;
        }
        else if(std::regex_match(source_line, base_match, xor_gate))
        {
        	sscanf(source_line.c_str(), "P V%d = V%lld XOR V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = xor_gate_id;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
        }
        else if(std::regex_match(source_line, base_match, naab_gate))
        {
        	sscanf(source_line.c_str(), "P V%d = V%lld NAAB V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = naab_gate_id;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
        }
        else if(std::regex_match(source_line, base_match, minus_gate))
        {
        	sscanf(source_line.c_str(), "P V%d = V%lld minus V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = minus_gate_id;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
        }
        else if(std::regex_match(source_line, base_match, not_gate))
        {
        	sscanf(source_line.c_str(), "P V%d = V%lld NOT V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = not_gate_id;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
        }
		else if(std::regex_match(source_line, base_match, exp_sum_gate))
		{
			sscanf(source_line.c_str(), "P V%d = V%lld EXPSUM V%lld E", &tgt, &src0, &src1);
			DAG_gate g;
			g.is_output = false;
			g.ty = exp_sum_gate_id;
			g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
			for(int i = g.input0.second; i <= g.input1.second; ++i)
			{
            	sha256_dag.circuit[make_pair((int)'V', i)].outputs.push_back(g.id);
			}
		}
		else if(std::regex_match(source_line, base_match, bit_test_gate))
		{
			sscanf(source_line.c_str(), "P V%d = V%lld BIT V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.is_output = false;
            g.ty = bit_test_gate_id;
            g.id = make_pair((int)'V', (int)tgt);
            g.input0 = make_pair((int)'V', (int)src0);
            g.input1 = make_pair((int)'V', (int)src1);
            sha256_dag.circuit[make_pair((int)'V', tgt)] = g;
            sha256_dag.circuit[g.input0].outputs.push_back(g.id);
            sha256_dag.circuit[g.input1].outputs.push_back(g.id);
		}
        else
        {
            cout << source_line << endl;
            assert(false);
        }
    }
    
	DAG_to_layered();
}

DAG_circuit rdl_dag, rdl_dag_copy;

void read_rdl(ifstream &rdl_in)
{
	int output_count = 0;
	rdl.layers.resize(2);
	rdl.depth = 2;
	int min_output_id = 0x3f3f3f3f;
	map<int, int> output_gate_mapping;
    while(getline(rdl_in, source_line))
	{
		if(std::regex_match(source_line, base_match, constant_assign_gate))
		{
			sscanf(source_line.c_str(), "P V%d = %lld E", &tgt, &src0);
			DAG_gate g;
            g.ty = input;
            g.layered_lvl = 0;
            g.id = make_pair((int)'V', tgt);
            g.input0 = make_pair((int)'S', src0);
            rdl_dag.circuit[g.id] = g;
		}
		else if(std::regex_match(source_line, base_match, input_gate))
		{
			sscanf(source_line.c_str(), "P V%d = I%lld E", &tgt, &src0);
            DAG_gate g;
            g.ty = input;
            g.layered_lvl = 0;
            g.id = make_pair((int)'V', tgt);
            g.input0 = make_pair((int)'S', rand());
            rdl_dag.circuit[g.id] = g;
		}
		else if(std::regex_match(source_line, base_match, output_gate))
		{
			output_count++;
            //doesn't need to do anything
            sscanf(source_line.c_str(), "P O%d = V%lld E", &tgt, &src0);
            output_gate_mapping[src0] = tgt;
            min_output_id = min(min_output_id, tgt);
			continue;
		}
		else if(std::regex_match(source_line, base_match, pass_gate))
		{
            sscanf(source_line.c_str(), "P V%d = V%lld PASS V%lld E", &tgt, &src0, &src1);
            DAG_gate g;
            g.ty = relay_gate_id;
            g.layered_lvl = 1;
            g.id = make_pair((int)'V', tgt);
            g.input0 = make_pair((int)'V', src0);
            rdl_dag.circuit[g.id] = g;
		}
		else
		{
			cout << source_line << endl;
			assert(false);
		}
	}
	cout << sha256.layers[0].gates.size() << endl;
    cout << input_count << " " << output_count << endl;
    repeat_num = output_count / input_count;
    assert(input_count * repeat_num == output_count);
    int max_output_id = input_count;
    int layer_count[2];
    layer_count[0] = layer_count[1] = 0;
    for(auto i = rdl_dag.circuit.begin(); i != rdl_dag.circuit.end(); ++i)
    {
    	auto &g = i -> second;
    	if(g.layered_lvl == 0)
    		g.layered_id = layer_count[0]++;
    	else
		{
			int block_num = (output_gate_mapping[g.id.second] - min_output_id) / input_count;
			int id = block_num * sha256.layers[0].gates.size() + (output_gate_mapping[g.id.second] - min_output_id) % input_count;
			g.layered_id = id;
		}
    }
    
    for(auto i = rdl_dag.circuit.begin(); i != rdl_dag.circuit.end(); ++i)
    {
    	auto &g = i -> second;
    	if(g.layered_lvl == 0)
    	{
    		gate layered_gate;
    		layered_gate.ty = input;
    		layered_gate.g = g.layered_id;
    		layered_gate.u = g.input0.second;
    		layered_gate.v = 0;
    		rdl.layers[0].gates.push_back(layered_gate);
    	}
    }
    
    int lgc = rdl.layers[0].gates.size();
    int full_layer_count = 1;
    rdl.layers[0].bit_len = 0;
    while(lgc)
    	full_layer_count *= 2, lgc /= 2, rdl.layers[0].bit_len++;
    lgc = rdl.layers[0].gates.size();
    rdl.layers[0].is_parallel = false;
    for(int i = lgc; i < full_layer_count; ++i)
    {
    	gate layered_gate;
    	layered_gate.ty = dummy;
    	layered_gate.g = i;
    	layered_gate.u = layered_gate.v = 0;
    	rdl.layers[0].gates.push_back(layered_gate);
    }
    
    
    rdl.layers[1].is_parallel = false;
    rdl.layers[1].gates.resize(sha256.layers[0].gates.size() * repeat_num);
    
    rdl_dag_copy = rdl_dag;
    
    for(auto i = rdl_dag_copy.circuit.begin(); i != rdl_dag_copy.circuit.end(); ++i)
    {
    	auto &g = i -> second;
    	if(g.layered_lvl == 1)
    	{
    		gate layered_gate;
    		layered_gate.ty = relay_gate_id;
    		layered_gate.g = g.layered_id;
    		layered_gate.u = rdl_dag.circuit[g.input0].layered_id;
    		layered_gate.v = 0;
    		rdl.layers[1].gates[layered_gate.g] = layered_gate;
    	}
    }
    
    for(int i = 0; i < repeat_num; ++i)
    {
		for(int j = 0; j < padding_num[0]; ++j)
		{
			int id = i * sha256.layers[0].gates.size() + j + max_output_id;
			gate layered_gate;
			layered_gate.ty = dummy;
			layered_gate.g = id;
			layered_gate.u = layered_gate.v = 0;
			rdl.layers[1].gates[id] = layered_gate;
		}
    }
}

void merge_and_output(const char *output_path, const char *meta_output_path)
{
	int d = rdl.layers.size() + sha256.layers.size();
	FILE *sha256_circuit_file = fopen(output_path, "w");
	FILE *meta = fopen(meta_output_path, "w");
	
	fprintf(sha256_circuit_file, "%d\n", d);
	fprintf(sha256_circuit_file, "%d ", (int)rdl.layers[0].gates.size());
	for(int i = 0; i < rdl.layers[0].gates.size(); ++i)
	{
		fprintf(sha256_circuit_file, "%d %d %015lld %lld ", input, rdl.layers[0].gates[i].g, rdl.layers[0].gates[i].u, rdl.layers[0].gates[i].v);
	}
	
	fprintf(meta, "0 0 1 0 0\n");
	
	fprintf(sha256_circuit_file, "\n%d ", (int)rdl.layers[1].gates.size());
	
	for(int i = 0; i < rdl.layers[1].gates.size(); ++i)
	{
		fprintf(sha256_circuit_file, "%d %d %015lld %lld ", rdl.layers[1].gates[i].ty, rdl.layers[1].gates[i].g, rdl.layers[1].gates[i].u, rdl.layers[1].gates[i].v);
	}
	
	int log_rep = 0, tmp = repeat_num;
	while(tmp != 1)
		log_rep++, tmp /= 2;
	
	fprintf(meta, "0 %d %d %d %d\n", (int)sha256.layers[0].gates.size(), repeat_num, sha256.layers[0].bit_len, log_rep);
	
	fprintf(sha256_circuit_file, "\n%d ", (int)sha256.layers[0].gates.size() * repeat_num);
	int block_size;
	for(int r = 0; r < repeat_num; ++r)
	{
		block_size = sha256.layers[0].gates.size();
		for(int i = 0; i < sha256.layers[0].gates.size(); ++i)
		{
			if(sha256.layers[0].gates[i].ty == input)
			{
				fprintf(sha256_circuit_file, "%d %d %015lld %lld ", relay_gate_id, sha256.layers[0].gates[i].g + r * block_size, (long long)sha256.layers[0].gates[i].g + r * block_size, (long long)0);
			}
			else if(sha256.layers[0].gates[i].ty == dummy)
			{
				fprintf(sha256_circuit_file, "%d %d %015lld %lld ", dummy, sha256.layers[0].gates[i].g + r * block_size, (long long)0, (long long)0);
			}
			else
				assert(false);
		}
	}
	
	
	fprintf(meta, "1 %d %d %d %d\n", (int)sha256.layers[0].gates.size(), repeat_num, sha256.layers[0].bit_len, log_rep);
	
	for(int i = 1; i < sha256.layers.size(); ++i)
	{
		int prev_block_size = sha256.layers[i - 1].gates.size();
		block_size = sha256.layers[i].gates.size();
		fprintf(sha256_circuit_file, "\n%d ", (int)sha256.layers[i].gates.size() * repeat_num);
		for(int r = 0; r < repeat_num; ++r)
		{
			for(int j = 0; j < sha256.layers[i].gates.size(); ++j)
			{
				if(sha256.layers[i].gates[j].ty == relay_gate_id || sha256.layers[i].gates[j].ty == not_gate_id)
				{
					assert(sha256.layers[i].gates[j].v == 0);
					fprintf(sha256_circuit_file, "%d %d %015lld %lld ", sha256.layers[i].gates[j].ty, sha256.layers[i].gates[j].g + r * block_size, sha256.layers[i].gates[j].u + r * prev_block_size, sha256.layers[i].gates[j].v);
				}
				else
				{
					fprintf(sha256_circuit_file, "%d %d %015lld %lld ", sha256.layers[i].gates[j].ty, sha256.layers[i].gates[j].g + r * block_size, sha256.layers[i].gates[j].u + r * prev_block_size, sha256.layers[i].gates[j].v + r * prev_block_size);
				}
			}
		}
		fprintf(meta, "1 %d %d %d %d\n", (int)sha256.layers[i].gates.size(), repeat_num, sha256.layers[i].bit_len, log_rep);
	}
	
	fclose(sha256_circuit_file);
	fclose(meta);
}

int main(int argc, char* argv[])
{
	ifstream circuit_in (argv[1]);
    ifstream rdl_in(argv[2]);
	
    read_circuit(circuit_in);
    read_rdl(rdl_in);
    
    merge_and_output(argv[3], argv[4]);
    
    rdl_in.close();
	circuit_in.close();
	return 0;
}
