#include <cstdio>
#include "linear_code/linear_code_encode.h"

int main(int argc, char* argv[])
{
    int N;
    sscanf(argv[1], "%d", &N);

    expander_init(N / column_size);

    return 0;
}