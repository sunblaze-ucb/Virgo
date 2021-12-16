#define MPI_ENABLED
#include "include/linear_gkr/prime_field.h"
#include <mpi.h>
#include <iostream>
#include "include/linear_gkr/d_verifier.h"


using namespace std;

MPI_Datatype mpiint128_t;
MPI_Datatype mpiu256_t;
MPI_Datatype mpiu512_t;
MPI_Datatype mpifield_element_t;
MPI_Datatype mpilinear_poly_t;
int my_rank;

void MPI_type_init()
{   
    MPI_Type_contiguous(2,MPI_UNSIGNED_LONG_LONG,&mpiint128_t);
    MPI_Type_commit(&mpiint128_t);

    //u256
    prime_field::u256b u256ele;
    MPI_Datatype u256_type[3] = { MPI_UNSIGNED_LONG_LONG, MPI_UNSIGNED_LONG_LONG, mpiint128_t};
    int u256_block_len[3] = {1, 1, 1};
    MPI_Aint u256_disp[3];
    u256_disp[0] = (MPI_Aint)&u256ele.lo - (MPI_Aint)&u256ele;
    u256_disp[1] = (MPI_Aint)&u256ele.mid - (MPI_Aint)&u256ele;
    u256_disp[2] = (MPI_Aint)&u256ele.hi - (MPI_Aint)&u256ele;
    MPI_Type_create_struct(3, u256_block_len, u256_disp, u256_type, &mpiu256_t);
    MPI_Type_commit(&mpiu256_t);

    //u512
    prime_field::u512b u512ele;
    MPI_Datatype u512_type[3] = { mpiint128_t, mpiint128_t, mpiu256_t};
    int u512_block_len[3] = {1, 1, 1};
    MPI_Aint u512_disp[3];
    u512_disp[0] = (MPI_Aint)&u512ele.lo - (MPI_Aint)&u512ele;
    u512_disp[1] = (MPI_Aint)&u512ele.mid - (MPI_Aint)&u512ele;
    u512_disp[2] = (MPI_Aint)&u512ele.hi - (MPI_Aint)&u512ele;
    MPI_Type_create_struct(3, u512_block_len, u512_disp, u512_type, &mpiu512_t);
    MPI_Type_commit(&mpiu512_t);

    //prime_field::field_element
    prime_field::field_element ele;
    MPI_Datatype ele_type[1] = { mpiu512_t};
    int ele_block_len[1] = {1};
    MPI_Aint ele_disp[1];
    ele_disp[0] = (MPI_Aint)&ele.value - (MPI_Aint)&ele;
    MPI_Type_create_struct(1, ele_block_len, ele_disp, ele_type, &mpifield_element_t);
    MPI_Type_commit(&mpifield_element_t);

    //linear poly
    linear_poly linear_polynomial;
    MPI_Datatype poly_type[2] = { mpifield_element_t, mpifield_element_t};
    int linear_polynomial_block_len[2] = {1, 1};
    MPI_Aint linear_polynomial_disp[2];
    linear_polynomial_disp[0] = (MPI_Aint)&linear_polynomial.a - (MPI_Aint)&linear_polynomial;
    linear_polynomial_disp[1] = (MPI_Aint)&linear_polynomial.b - (MPI_Aint)&linear_polynomial;
    MPI_Type_create_struct(2, linear_polynomial_block_len, linear_polynomial_disp, poly_type, &mpilinear_poly_t);
    MPI_Type_commit(&mpilinear_poly_t);
}

void MPI_type_test()
{
    __uint128_t fixed_tester;
    
    fixed_tester = 1LL << 62;
    fixed_tester <<= 30;
    fixed_tester |= 1LL << 32;
    //uint128_t
    if(my_rank == 0) //sender
    {
        MPI_Send(&fixed_tester, 1, mpiint128_t, 1, 0, MPI_COMM_WORLD);
    }
    else if(my_rank == 1) //receiver
    {
        __uint128_t recv_x;
        MPI_Recv(&recv_x, 1, mpiint128_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        if(recv_x != fixed_tester)
        {
            printf("int128 Transmission error\n");
        }
        else
        {
            printf("int128 Transmission succ\n");
        }
    }

    //u256
    prime_field::u256b u256_fix_tester;
    u256_fix_tester.lo = 1234532;
    u256_fix_tester.mid = 58975456;
    u256_fix_tester.hi = fixed_tester;

    if(my_rank == 0) //sender
    {
        MPI_Send(&u256_fix_tester, 1, mpiu256_t, 1, 0, MPI_COMM_WORLD);
    }
    else if(my_rank == 1) //receiver
    {
        prime_field::u256b recv_u256;
        MPI_Recv(&recv_u256, 1, mpiu256_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        if(recv_u256.lo != u256_fix_tester.lo || recv_u256.mid != u256_fix_tester.mid || recv_u256.hi != u256_fix_tester.hi)
        {
            printf("int256 Transmission error\n");
        }
        else
        {
            printf("int256 Transmission succ\n");
        }
    }

    //u512
    prime_field::u512b u512_fix_tester;
    u512_fix_tester.lo = fixed_tester;
    u512_fix_tester.mid = fixed_tester + 1;
    u512_fix_tester.hi = u256_fix_tester;

    if(my_rank == 0) //sender
    {
        MPI_Send(&u512_fix_tester, 1, mpiu512_t, 1, 0, MPI_COMM_WORLD);
    }
    else if(my_rank == 1) //receiver
    {
        prime_field::u512b recv_u512;
        MPI_Recv(&recv_u512, 1, mpiu512_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        if(recv_u512 != u512_fix_tester)
        {
            printf("int512 Transmission error\n");
        }
        else
        {
            printf("int512 Transmission succ\n");
        }
    }

    //prime_field::field_element
    prime_field::field_element fixed_ele;
    fixed_ele.value = u512_fix_tester;
    
    if(my_rank == 0) //sender
    {
        MPI_Send(&fixed_ele, 1, mpifield_element_t, 1, 0, MPI_COMM_WORLD);
    }
    else if(my_rank == 1) //receiver
    {
        prime_field::field_element recv_ele;
        MPI_Recv(&recv_ele, 1, mpifield_element_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        if(recv_ele != fixed_ele)
        {
            printf("element Transmission error\n");
        }
        else
        {
            printf("element Transmission succ\n");
        }
    }

    //linear_poly
    linear_poly fixed_poly;
    fixed_poly.a = fixed_ele;
    fixed_poly.b = fixed_ele + 1;

    if(my_rank == 0) //sender
    {
        MPI_Send(&fixed_poly, 1, mpilinear_poly_t, 1, 0, MPI_COMM_WORLD);
    }
    else if(my_rank == 1) //receiver
    {
        linear_poly recv_poly;
        MPI_Recv(&recv_poly, 1, mpilinear_poly_t, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        if(recv_poly.a != fixed_poly.a || recv_poly.b != fixed_poly.b)
        {
            printf("linear_poly Transmission error\n");
            assert(false);
        }
        else
        {
            printf("linear_poly Transmission succ\n");
        }
    }
}

zk_verifier v;
zk_prover p;

int main(int argc, char* argv[])
{
    prime_field::init("21888242871839275222246405745257275088548364400416034343698204186575808495617", 10);
    v.get_prover(&p);
    MPI_Init(&argc, &argv);


    // Get the number of processes
    int size;
    MPI_Comm_size(MPI_COMM_WORLD, &size);
    MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
    
    MPI_type_init();
    MPI_type_test();
    
    v.set_rank(my_rank, size);
    p.set_rank(my_rank, size);
    v.read_circuit(argv[1], argv[2]);
    v.read_witness(argv[4], my_rank);

    p.get_circuit(v.C);
    bool result = v.verify(argv[3]);

    printf("rank %d, %s\n", my_rank, result ? "Pass" : "Fail");
    MPI_Finalize();

    return 0;
}