#include <cstdlib>
#include <iostream>
#include <time.h>
#include <stdlib.h>
#include <vector>
#include <fstream>
#include <gmp.h>
#include <gmpxx.h>
#include <cmath>

using namespace std;

typedef int (*fptr)(int);

typedef struct circ
{
	struct level* levels;
	int num_levels; //number of levels of circuit
}circ;

typedef struct level
{

	fptr in1;
	fptr in2;
	fptr types;
	vector<mpz_class> gates={0};
	int S; 
	int logS;

}level;

int d;
mpz_class p;
mpz_class rdomain;

unsigned long int seed;
gmp_randstate_t r_state;

mpz_class extrap(vector<mpz_class> vec, int n, mpz_class r){
  mpz_class result=0;
  mpz_class mult=1;
  for(int i = 0; i < n; i++){
    mult=1;
    for(int j=0; j < n; j++)
    {
		if(i!=j){
			mpz_class temp, temp2 = (i-j)%p;
			mpz_invert(temp.get_mpz_t(), temp2.get_mpz_t(), p.get_mpz_t());
			
			mult = mult*(r-j)*temp;
		}
    }
    result=result+mult*vec[i];
	
  }
  result = result%p;
  
  return result;
}

//fills in high-order variable xi wih ri
void updateV(vector<mpz_class>* V, int num_new, mpz_class ri){
	for(int i = 0; i < num_new; i++)
	{
		if((*V)[i]!=0)
			(*V)[i]*=(1-ri);
		if((*V)[i+num_new]!=0)
			(*V)[i]+=(*V)[i+num_new]*ri;
		if((*V)[i]!=0)
			(*V)[i]%=p;
		//(*V)[i] = ((*V)[i]*(1-ri) + (*V)[i+num_new]*ri)%p;
	}
	
	(*V).resize(num_new);
}

//sets betavals(p) = \prod_{i=0}^{d-1} (zipi + (1-zi)(1-pi))
void initialize_betavals(vector<mpz_class>* betavals, int d, vector<mpz_class> z){
	
	(*betavals)[0]=1;
	mpz_class zval;
	int two_to_k = 1;
	mpz_class oldval;
	for(int k = d-1; k >=0 ; k--)
	{
		zval = z[k];
		for(int i = 0; i < two_to_k; i++)
		{
			oldval = (*betavals)[i];
			(*betavals)[i] = (oldval*(1-zval))%p;
			(*betavals)[i + two_to_k] = (oldval*zval)%p;
		}
		
		
		two_to_k = two_to_k * 2;
	}
}

void update_betavals(vector<mpz_class>* betavals, int num_new, mpz_class zval, mpz_class rval){
    mpz_class update = zval*rval + (1-zval)*(1-rval);
    mpz_class temp, temp2=(1-zval)%p;
	mpz_invert(temp.get_mpz_t(), temp2.get_mpz_t(), p.get_mpz_t());

    
	for(int i = 0; i < num_new; i++)
	{
		(*betavals)[i] = ((*betavals)[i]*temp)%p;
		(*betavals)[i] = ((*betavals)[i]*update)%p;
	}
	
	(*betavals).resize(num_new);
}


//compute the MLE of V at a point r. size of r is log(size of V). 
mpz_class random_V_L(vector<mpz_class>& V, vector<mpz_class>& r){
	vector<mpz_class> Z;
	Z.resize((int)pow(2,r.size()));
	Z[0]=1;
	int two_to_k = 1;
	mpz_class oldval;
	for(int k = r.size()-1; k >=0 ; k--)
	{
		
		for(int i = 0; i < two_to_k; i++)
		{
			oldval = Z[i];
			Z[i] = (oldval*(1-r[k]))%p;
			Z[i + two_to_k] = (oldval*r[k])%p;
		}
		
		
		two_to_k = two_to_k * 2;
	}
	
	mpz_class ri = 0;
	
	for(int i=0;i<V.size();i++){
	
		ri+=Z[i]*V[i];
		ri%=p;
	}
	return ri;

}

mpz_class sum_check_mm(circ* c, int index, vector<mpz_class>* z, mpz_class ri, int* com_ct, int* rd_ct){
	
	
	vector<mpz_class> r;
	r.resize(d*3+1);
	
	for(int i = 0; i < r.size(); i++)
	{
		mpz_urandomm(r[i].get_mpz_t(),r_state,rdomain.get_mpz_t());
	}
	
	
	vector<vector<mpz_class> > poly;
	poly.resize(d*3);
	
	for(int i=0;i<poly.size();i++){
		poly[i].resize(4);
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3]= 0;
	}
	
	
	*com_ct = *com_ct+3*2*d + 4*d;
	*rd_ct = *rd_ct+d*3 + 1;
	
	int n=pow(2,d);
	
	int num_terms = n*n*n;
	
	vector<mpz_class> betavals;
	betavals.resize(n*n*n);
	
	initialize_betavals(&betavals, d*3, *z);
	
	
	mpz_class betar;
	
	mpz_class betaupdate;
	//set num_is to n if we're multiplying nxn matrices
	int num_is = n;
	int num_js = n;
	int num_ks = n;
	int ik;
	int jk;
	int ijk;
	
	mpz_class multby0;
	mpz_class multby1;
	mpz_class multby2;
	
	mpz_class temp_inv1;
	mpz_class temp_inv2;
	
	vector<mpz_class> V0(n*n), V1(n*n);
	copy(c->levels[index+1].gates.begin(), c->levels[index+1].gates.begin()+n*n, V0.begin());
	copy(c->levels[index+1].gates.begin()+n*n, c->levels[index+1].gates.begin()+2*n*n, V1.begin());
	
	for(int round = 0; round < d; round++)
	{
		betaupdate = ((*z)[3*d-1-round]*2-(1-(*z)[3*d-1-round]));
		mpz_invert(temp_inv1.get_mpz_t(), (*z)[3*d-1-round].get_mpz_t(), p.get_mpz_t());
		mpz_class temp = (1-(*z)[3*d-1-round])%p;
		
		mpz_invert(temp_inv2.get_mpz_t(), (temp).get_mpz_t(), p.get_mpz_t());
		
		
		for(int i = 0; i < num_is; i++)
		{
			for(int k = 0; k < n; k++)
			{
				ik = (i << d) + k;
				multby0=multby1=multby2=0;
				
				for(int j = 0; j < n; j++)
				{
					jk = (j << d)+k;
					ijk= (i << (2*d)) + jk;
					
					if(i & (num_is >> 1))
					{							
						multby1= (multby1+betavals[ijk]*V1[jk]);
						betar = (betavals[ijk]*temp_inv1);
						betar = (betar*betaupdate);
						multby2 = (multby2 + 2*betar*V1[jk]);
					}
					else
					{						
						multby0 = (multby0 + betavals[ijk]*V1[jk]);
						betar = (betavals[ijk]*temp_inv2);
						betar = (betar*betaupdate);
						multby2 = (multby2 + (-betar)*V1[jk]);  
					}
				}//end j loop
				poly[round][0] = poly[round][0] + V0[ik]*multby0;
				poly[round][1] = poly[round][1] + V0[ik]*multby1;
				poly[round][2] = poly[round][2] + V0[ik]*multby2;
			}//end k loop
		}//end i loop
		
		poly[round][0]%=p;
		poly[round][1]%=p;
		poly[round][2]%=p;
		
		num_is = num_is >> 1;
		update_betavals(&betavals, num_is*n*n, (*z)[d*3-1-round], r[d*3-1-round]);
		updateV(&V0, num_is * n, r[d*3-1-round]);
	}
	
	for(int round = d; round < 2*d; round++)
	{
		betaupdate = ((*z)[3*d-1-round]*2-(1-(*z)[3*d-1-round]));
		mpz_invert(temp_inv1.get_mpz_t(), (*z)[3*d-1-round].get_mpz_t(), p.get_mpz_t());
		mpz_class temp = (1-(*z)[3*d-1-round])%p;
		
		mpz_invert(temp_inv2.get_mpz_t(), (temp).get_mpz_t(), p.get_mpz_t());
		

		for(int k = 0; k < n; k++)
		{
			multby0=multby1=multby2=0;
			for(int j = 0; j < num_js; j++)
			{
				ik = k;
				jk = (j << d)+k;
				ijk= jk;
					
				if(j & (num_js >> 1))
				{
					multby1= (multby1 + betavals[ijk]*V1[jk]);
					betar = (betavals[ijk]*temp_inv1);
					betar = (betar*betaupdate);
					multby2 = (multby2 + 2*betar*V1[jk]);
				}
				else
				{
					multby0 = (multby0 + betavals[ijk]*V1[jk]);
					betar = (betavals[ijk]*temp_inv2);
					betar = (betar*betaupdate);
					multby2 = (multby2 + (-betar)*V1[jk]);  
				}
			}//end k loop
			poly[round][0] = poly[round][0] + V0[ik]*multby0;
			poly[round][1] = poly[round][1] + V0[ik]*multby1;
			poly[round][2] = poly[round][2] + V0[ik]*multby2;
		}//end j loop
		
		poly[round][0]%=p;
		poly[round][1]%=p;
		poly[round][2]%=p;
		num_js = num_js >> 1;
		update_betavals(&betavals, num_js*n, (*z)[3*d-1-round], r[3*d-1-round]);
		updateV(&V1, num_js * n, r[3*d-1-round]);
	}//end round loop
	
	mpz_class betaupdate2;
	mpz_class betaupdate3;
	mpz_class betar2;
	mpz_class betar3;
	for(int round = 2*d; round < 3*d; round++)
	{
		betaupdate2 = (((*z)[d*3-1-round]-1) + 2*(*z)[d*3-1-round]);
		betaupdate3 = (2*((*z)[3*d-1-round]-1) + 3*(*z)[3*d-1-round])%p;
		mpz_invert(temp_inv1.get_mpz_t(), (*z)[3*d-1-round].get_mpz_t(), p.get_mpz_t());
		mpz_class temp = (1-(*z)[3*d-1-round])%p;
		mpz_invert(temp_inv2.get_mpz_t(), (temp).get_mpz_t(), p.get_mpz_t());
		
		for(int k = 0; k < num_ks; k++)
		{
			ik = k;
			jk = k;
			ijk= k;
					
			if(k & (num_ks >> 1))
			{
				poly[round][1] = poly[round][1] + betavals[ijk]*V0[ik]*V1[jk];
				betar = (betavals[ijk]* temp_inv1);
				betar2 = (betar* betaupdate2);
				poly[round][2] = poly[round][2] + betar2* 2*V0[ik]*(2*V1[jk] - V1[jk-(num_ks>>1)]);
				betar3 = (betar* betaupdate3);
				poly[round][3] = poly[round][3] + betar3*3*V0[ik]*(3*V1[jk]-2*V1[jk-(num_ks>>1)]);
			}
			else
			{
				poly[round][0] = poly[round][0] + betavals[ijk]*V0[ik]*V1[jk];
				betar = (betavals[ijk]*temp_inv2);
				betar2 = (betar* betaupdate2);
				poly[round][2] = poly[round][2] + betar2*(-V0[ik])*(2*V1[jk+(num_ks>>1)]-V1[jk]);
				betar3 = (betar* betaupdate3);
				poly[round][3] = poly[round][3] + betar3*(-2*V0[ik])*(-2*V1[jk]+3*V1[jk+(num_ks>>1)]);   
			}
		}//end k loop
		
		poly[round][0]%=p;
		poly[round][1]%=p;
		poly[round][2]%=p;
		num_ks = num_ks >> 1;
		update_betavals(&betavals, num_ks, (*z)[3*d-1-round], r[3*d-1-round]);
		updateV(&V0, num_ks, r[3*d-1-round]);
		updateV(&V1, num_ks, r[3*d-1-round]);
	}//end round loop
	
	if((poly[0][0]+poly[0][1])%p != ri && (poly[0][0]+poly[0][1])%p+p != ri && (poly[0][0]+poly[0][1])%p-p != ri)
	{
		cout << "poly[0][0]+poly[0][1] != ri. poly[0][0] is: " << poly[0][0] << " poly[0][1] is: ";
		cout << poly[0][1] << " ri is: " << ri << " i is: " << index << endl;
	}
	
	mpz_class check;
	for(int j =1; j <d*2; j++)
	{
		check=extrap(poly[j-1], 3, r[3*d-1-j-1]);  
		if(check != (poly[j][0]+poly[j][1])%p && check != (poly[j][0]+poly[j][1])%p+p && check != (poly[j][0]+poly[j][1])%p-p)
		{
			cout << " j is: " << j << "; poly[j][0]+poly[j][1] != extrap. poly[j][0] is: " << poly[j][0] << " poly[j][1] is: ";
			cout << poly[j][1] << " extrap is: " << check <<" index is: " << index << endl; 
		}
	}
	
	for(int j =2*d; j <3*d; j++)
	{
		check=extrap(poly[j-1], 4, r[3*d-1-j-1]);  
		if(check != (poly[j][0]+poly[j][1])%p && check != (poly[j][0]+poly[j][1])%p+p && check != (poly[j][0]+poly[j][1])%p-p)
		{
			cout << " j is: " << j << "; poly[j][0]+poly[j][1] != extrap. poly[j][0] is: " << poly[j][0] << " poly[j][1] is: ";
			cout << poly[j][1] << " extrap is: " << check <<" index is: " << index << endl; 
		}
	}
	
	/*
	if( (myMod(poly[0][0] + poly[0][1]) != ri) && (myMod(poly[0][0] + poly[0][1]) != ri + PRIME) && 
		((myMod(poly[0][0] + poly[0][1]) + PRIME) != ri))
	{
		cout << "first check failed in checking final layer when ni was " << ni << endl;
		cout << "ri was " << ri << " PRIME-ri was " << PRIME-ri << endl;
		cout << "poly[0][0] was " << poly[0][0] << " and poly[0][1] was " << poly[0][1] << " and their sum was " << myMod(poly[0][0] + poly[0][1]) << endl;
		//exit(1);
	}

	uint64 extrap_val = extrap(poly[0], 3, r[d-1]);
	for(int round = 1; round < 2*logn; round++)
	{
		if( (myMod(poly[round][0] + poly[round][1]) != extrap_val) && (myMod(poly[round][0] + poly[round][1]) != extrap_val + PRIME) &&
			((myMod(poly[round][0] + poly[round][1]) + PRIME) != extrap_val)) 
		{
			cout << "check for round " << round << " failed in checking final layer when ni was " << ni << endl;
			cout << "extrap_val was " << extrap_val << " and PRIME-extrap_val was: " << PRIME-extrap_val << endl;
			cout << "poly[round][0] was " << poly[round][0] << " and poly[round][1] was " << poly[round][1] << " and their sum was " << myMod(poly[round][0] + poly[round][1]) << endl;
			//exit(1);
	 	}
	 	extrap_val = extrap(poly[round], 3, r[d-1-round]);
	 }
	 
	for(int round = 2*logn; round < 3*logn; round++)
	{
		if( (myMod(poly[round][0] + poly[round][1]) != extrap_val) && (myMod(poly[round][0] + poly[round][1]) != extrap_val + PRIME) &&
			((myMod(poly[round][0] + poly[round][1]) + PRIME) != extrap_val)) 
		{
			cout << "check for round " << round << " failed in checking final layer when ni was " << ni << endl;
			cout << "extrap_val was " << extrap_val << " and PRIME-extrap_val was: " << PRIME-extrap_val << endl;
			cout << "poly[round][0] was " << poly[round][0] << " and poly[round][1] was " << poly[round][1] << " and their sum was " << myMod(poly[round][0] + poly[round][1]) << endl;
			cout << " and poly[round-1][2] which should equal extrap_val was: " << poly[round-1][2] << endl;
			//exit(1);
	 	}
	 	extrap_val = extrap(poly[round], 4, r[d-1-round]);
	 }
	 
	 
	 //now P "tells" V \tilde{A}(r) and \tilde{B^T}(r') and V checks final message based on this
	 //i.e. V checks g_{d-1}(r) = beta(z, p) \tilde{A}(r_{d-1}, ..., r1, r0) \tilde{B^T}(r_{d-1}, ..., r0) 
	 //If so, V believes P as long as \tilde{A}(r) and \tilde{B^T}(r') are as claimed
	 
	 uint64 correct_out = myModMult(betavals[0], myModMult(V0[0], V1[0]));
	 if( (correct_out != extrap_val) && (correct_out + PRIME != extrap_val) && (correct_out != extrap_val + PRIME))
	 {
	 	cout << "correct_out != extrap_val in check for final layer. correct_out is " << correct_out << " and extrap_val is: " << extrap_val << endl;
	 	//exit(1);
	 }
	 */
	 
	ri = V0[0]*(1-r[d*3])+V1[0]*(r[d*3]);
	(*z) = r;
	
	
	return ri;

}


mpz_class sum_check_addtree(circ* c, int index, vector<mpz_class>* z, mpz_class ri, int* com_ct, int* rd_ct){
	vector<mpz_class> r(c->levels[index].logS+1);
	
	for(int i=0;i<r.size()-1;i++){
		r[i] = (*z)[i];
	}
	
	vector<mpz_class> Z((int)pow(2,r.size()-1));
	Z[0]=1;
	int two_to_k = 1;
	mpz_class oldval;
	for(int k = r.size()-2; k >=0 ; k--)
	{
		
		for(int i = 0; i < two_to_k; i++)
		{
			oldval = Z[i];
			Z[i] = (oldval*(1-r[k]))%p;
			Z[i + two_to_k] = (oldval*r[k])%p;
		}
		
		
		two_to_k = two_to_k * 2;
	}
	
	vector<mpz_class> V(2);
	V[0] = 0;
	V[1] = 0;
	
	for(int i=0;i<Z.size();i++){
		V[0]+=Z[i]*c->levels[index+1].gates[2*i];
		V[1]+=Z[i]*c->levels[index+1].gates[2*i+1];
	}
	
	if((V[0]+V[1])%p !=ri && (V[0]+V[1])%p+p !=ri && (V[0]+V[1])%p-p !=ri)
		cout<<"fail\n";
	
	mpz_urandomm(r[r.size()-1].get_mpz_t(),r_state,rdomain.get_mpz_t());
	
	mpz_class r3 = extrap(V,2,r[r.size()-1]);
	
	*rd_ct+=1;
	*com_ct+= 3;
	
	(*z) = r;
	return r3;
}


int input_type(int j){
	return -1;
}

int return0(int j){
	return 0;
}

int return1(int j){
	return 1;
}

int return_binary1(int j){
	return j*2;
}

int return_binary2(int j){
	return j*2+1;
}

int mm_in1(int p)
{
	//p is (i, j, k), where i is of length d. want to return (0, i, k)
	int all_ones = (int)pow(2, d)-1;
	int i = (p >> (2*d)) & all_ones;
	int k = p & all_ones;
	return (i << d) + k;
}

//d is number of bits in gate label
int mm_in2(int p)
{
	
    //all_ones is 2*d 1s
	int all_ones = (int)pow(2, 2*d)-1;
	//p is (i, j, k), where i is of length d. want to return (1, j, k)
	//j & all_ones is (0, k, j). adding all_ones+1 makes this (1, j, k)
	//cout << " and i am returning " << (p & all_ones) << " plus " << (all_ones + 1) << endl;
	return (p & all_ones) + (all_ones + 1);
}


circ* construct_circ_mm()
{                    
	
	int n = pow(2, d);
	
	int depth = d+2;
	circ* c = (circ*) malloc(sizeof(circ));
	c->levels = new level[depth];
	c->num_levels=depth;	
	
	c->levels[depth-1].S = n*n*2;
	c->levels[depth-1].logS = 2*d+1;
	c->levels[depth-1].types = input_type;
	
	c->levels[depth-1].gates.resize(c->levels[depth-1].S);
	
	
	for(int i=0;i<c->levels[depth-1].S;i++)
		c->levels[depth-1].gates[i]=rand()%10;
	
	
	{
		int i=depth-2;
		c->levels[i].S = n*n*n;
		c->levels[i].logS = 3*d;

		c->levels[i].in1 = mm_in1;
		c->levels[i].in2 = mm_in2;
		c->levels[i].types = return1;
		c->levels[i].gates.resize(c->levels[i].S);
		
	}
	
	for(int i=depth-3;i>=0;i--){
		c->levels[i].S = c->levels[i+1].S/2;
		c->levels[i].logS = c->levels[i+1].logS-1;

		c->levels[i].in1 = return_binary1;
		c->levels[i].in2 = return_binary2;
		c->levels[i].types = return0;
		
		c->levels[i].gates.resize(c->levels[i].S);
	
	}
		
	
	return c;
}



long long evaluate_circuit(circ* c)
{
	int d = c->num_levels-1;
	mpz_class val1,val2;


	int di;
	int in1;
	int in2;
	int type;
	
	long long gatenum=0;
	
	for(int i = d-1; i >= 0; i--){
				
		for(int j = 0; j < c->levels[i].S; j++){
	
			in1 = c->levels[i].in1(j);
			in2 = c->levels[i].in2(j);
			type = c->levels[i].types(j);
			
			if(type==1 || type == 100)
				gatenum++;
			
			val1=c->levels[i+1].gates[in1];
			val2=c->levels[i+1].gates[in2]; 
			
			
			
			if(type == 0){
				c->levels[i].gates[j]=(val1+val2)%p;
			}
			else if(type == 1){
				c->levels[i].gates[j]=(val1*val2)%p;
			}
			else{}
		}
	}
	
	return gatenum;
}

void print_circuit(circ* c){
	for(int l=c->num_levels-1;l>=0;l--){

	
	
		
			for(int i=0;i<c->levels[l].S;i++){
				cout<<c->levels[l].gates[i]<<",";
			}

		cout<<endl;
		cout<<endl; 
	}
	
	cout<<endl; 

}

int main(int argc, char** argv){
	
	
    seed = rand();
    gmp_randinit_default (r_state);
    gmp_randseed_ui(r_state, seed);
	
	rdomain.set_str("340282366920938463463374607431768211455",10); //2^128-1
	
	//generate random 254-bit prime. replace with p in ate-pairing
	
	p.set_str("16798108731015832284940804142231733909759579603404752749028378864165570215949",10);
	

	d=atoi(argv[1]);
	
	int n = (int)pow(2,d);
	
	int com_ct=0;
	int rd_ct=0;
	
	double ptime=0.0;
	long long gatenum = 0;
	
	circ* c = construct_circ_mm();
	

	gatenum+=evaluate_circuit(c);
	
	//print_circuit(c);
	
	
	vector<mpz_class> V_temp;
	
	vector<mpz_class> z;
	z.resize(c->levels[0].logS);
	for(int i=0;i<z.size();i++)
		mpz_urandomm(z[i].get_mpz_t(),r_state,rdomain.get_mpz_t());
	
	V_temp=c->levels[0].gates;
	
	mpz_class ri = random_V_L(V_temp,z);
	
	clock_t t1=clock();
	
	for(int i=0;i<c->num_levels-1;i++){
		
		
		cout<<i<<endl;
		if(i==c->num_levels-2)
			ri = sum_check_mm(c, i, &z, ri, &com_ct, &rd_ct);
		else
			ri = sum_check_addtree(c, i, &z, ri, &com_ct, &rd_ct);
	}
	
	cout<<z.size()<<endl;
	z.resize(d*2+1);
	
	ptime+=(double)(clock()-t1)/CLOCKS_PER_SEC;

	V_temp=c->levels[c->num_levels-1].gates;

	
	if( (ri!= (random_V_L(V_temp, z)%p)) && ri!= (random_V_L(V_temp, z)%p)+p && ri!= (random_V_L(V_temp, z)%p)-p)
		cout<<"V(L(x)) fails!\n";
	
		
	cout<<ptime<<"s total!!\n";
	cout<<gatenum<<" gates!"<<endl;
	
	
}
