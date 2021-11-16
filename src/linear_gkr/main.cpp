#define __debug__
#define __timer__
#include "linear_gkr/verifier.h"
#include "linear_gkr/prover.h"
#include "linear_gkr/prime_field.h"
#include <iostream>
#include <cassert>
zk_verifier v;
zk_prover p;

int main(int argc, char** argv)
{
	prime_field::init("21888242871839275222246405745257275088548364400416034343698204186575808495617", 10);
	p.total_time = 0;
	v.get_prover(&p);
	//std::cout << "come in" << std::endl;
	assert(argc == 4);
	v.read_circuit(argv[1], argv[2]);
	//std::cout << "after readfile" << std::endl;
	p.get_circuit(v.C);
	bool result = v.verify(argv[3]);
	printf("%s\n", result ? "Pass" : "Fail");
	return 0;
}