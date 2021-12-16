#include <cstdio>
#include <cstdlib>
#include <utility>
#include <cassert>
#include <vector>

using namespace std;

int main(int argc, char **argv)
{

	int mat_sz, num_copies;
	sscanf(argv[1], "%d", &mat_sz);
	sscanf(argv[5], "%d", &num_copies);
	FILE *output_path = fopen(argv[2], "w");
	FILE *meta_path = fopen(argv[3], "w");

	assert(__builtin_popcount(mat_sz) == 1);

	int log_mat_sz = 0;
	while(mat_sz != (1 << log_mat_sz))
		log_mat_sz++;
	
	//input layer
	int block_number = mat_sz * mat_sz;
	int block_size;
	vector<vector<int> > A, B;
	A.resize(mat_sz), B.resize(mat_sz);
	
	for(int i = 0; i < mat_sz; ++i)
	{
		A[i].resize(mat_sz);
		B[i].resize(mat_sz);
		for(int j = 0; j < mat_sz; ++j)
			A[i][j] = rand() % 10, B[i][j] = rand() % 10;
	}
	//input layer
	fprintf(output_path, "%d\n", 1 + 1 + 1);
	fprintf(output_path, "%d ", mat_sz * mat_sz * 2);
	for(int i = 0; i < mat_sz; ++i)
	{
		for(int j = 0; j < mat_sz; ++j)
		{
			fprintf(output_path, "%d %d %010d %d ", 3, i * mat_sz + j, A[i][j], 0);
		}
	}
	fprintf(meta_path, "0 0 1 0 0\n");
	for(int i = 0; i < mat_sz; ++i)
	{
		for(int j = 0; j < mat_sz; ++j)
		{
			fprintf(output_path, "%d %d %010d %d ", 3, mat_sz * mat_sz + i * mat_sz + j, B[i][j], 0);
		}
	}
	fprintf(output_path, "\n");

	//mult
	fprintf(output_path, "%d ", mat_sz * mat_sz * mat_sz);
	for(int i = 0; i < mat_sz; ++i)
	{
		for(int j = 0; j < mat_sz; ++j)
		{
			for(int k = 0; k < mat_sz; ++k)
			{
				int id = i * mat_sz * mat_sz + j * mat_sz + k;
				int a = i * k, b = k * j;
				fprintf(output_path, "%d %d %d %d ", 1, id, a, b);
			}
		}
	}
	fprintf(meta_path, "0 0 1 0 0\n");
	fprintf(output_path, "\n");

	

	//summation gate
	fprintf(output_path, "%d ", mat_sz * mat_sz);
	for(int i = 0; i < mat_sz; ++i)
	{
		for(int j = 0; j < mat_sz; ++j)
		{
			fprintf(output_path, "5 %d %d %d ", i * mat_sz + j, i * mat_sz * mat_sz + j * mat_sz, i * mat_sz * mat_sz + j * mat_sz + mat_sz);
		}
	}
	fprintf(meta_path, "0 0 1 0 0\n");
	fclose(output_path);
	fclose(meta_path);
	for(int i = 0; i < num_copies; ++i)
	{
		char wit_path[256];
		sprintf(wit_path, "%s_%d", argv[4], i);
		FILE *witness_file = fopen(wit_path, "w");
		for(int i = 0; i < 2 * mat_sz * mat_sz; ++i)
		{
			fprintf(witness_file, "%d ", rand());
		}
		fclose(witness_file);
	}
	return 0;
}
