// Exact field norm Q(sqrt(2),sqrt(3),sqrt(5),sqrt(7)) -> Q using GMP.
// A(R) is a polynomial in the 16-monomial basis with integer coefficients,
// ordered by bit mask for radicals [sqrt(2),sqrt(3),sqrt(5),sqrt(7)].
// Repeated conjugate-pair norms eliminate these radicals one at a time.
// For all polynomials, multiplication is exact using Kronecker substitution.
#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <stdexcept>
#include <cstdlib>
using namespace std;
using Z=mpz_class;
using Poly=vector<Z>;
size_t bits(const Z&x){return x==0?0:mpz_sizeinbase(x.get_mpz_t(),2);}
void trim(Poly&x){while(x.size()>1&&x.back()==0)x.pop_back();}
Poly add(const Poly&a,const Poly&b,int sign=1){Poly c(max(a.size(),b.size()),0);for(size_t i=0;i<a.size();i++)c[i]+=a[i];for(size_t i=0;i<b.size();i++)if(sign==1)c[i]+=b[i];else c[i]-=b[i];trim(c);return c;}
Poly scale(Poly p, long s){for(auto&x:p)x*=s;trim(p);return p;}
Poly mul(const Poly&a,const Poly&b){
 if(a.size()==1&&a[0]==0)return {0};if(b.size()==1&&b[0]==0)return {0};
 size_t maxa=0,maxb=0;for(const auto&x:a)maxa=max(maxa,bits(x));for(const auto&x:b)maxb=max(maxb,bits(x));
 size_t logn=0;while((1ULL<<logn)<=min(a.size(),b.size()))logn++;
 mp_bitcnt_t shift=maxa+maxb+logn+4; // each true coefficient magnitude < 2^(shift-2)
 Z A=0,B=0;
 for(size_t i=a.size();i-->0;){mpz_mul_2exp(A.get_mpz_t(),A.get_mpz_t(),shift);A+=a[i];}
 for(size_t i=b.size();i-->0;){mpz_mul_2exp(B.get_mpz_t(),B.get_mpz_t(),shift);B+=b[i];}
 Z product=A*B;
 const size_t n=a.size()+b.size()-1;
 Poly c(n);
 Z rem,half=Z(1)<<(shift-1),base=Z(1)<<shift;
 for(size_t i=0;i<n;i++){
   mpz_fdiv_r_2exp(rem.get_mpz_t(),product.get_mpz_t(),shift);
   if(rem>=half)rem-=base;
   c[i]=rem;
   product-=rem;
   mpz_fdiv_q_2exp(product.get_mpz_t(),product.get_mpz_t(),shift);
 }
 if(product!=0)throw runtime_error("Kronecker unpack overflow");
 trim(c);return c;
}
int main(int argc,char**argv){
 if(argc!=3){cerr<<"Usage: expand_norm <integer-G112-components.tsv> <output.tsv>\n";return 2;}
 ifstream f(argv[1]);if(!f)throw runtime_error("Cannot read input");
 string line;getline(f,line);vector<Poly> current(16,Poly(113));
 for(int power=0;power<=112;power++){
   if(!getline(f,line))throw runtime_error("Missing input row");
   istringstream ss(line);string item;getline(ss,item,'\t');if(stoi(item)!=power)throw runtime_error("Bad degree order");
   for(int mask=0;mask<16;mask++){
     if(!getline(ss,item,'\t'))throw runtime_error("Missing component");current[mask][power]=Z(item);
   }
 }
 const int rad[]={2,3,5,7};
 for(int stage=0;stage<4;stage++){
   int n=(int)current.size()/2;
   vector<Poly> next(n,Poly(2*(current[0].size()-1)+1,0));
   cerr<<"Eliminating sqrt("<<rad[stage]<<"), "<<n<<" output components; input degree "<<current[0].size()-1<<"\n";
   for(int i=0;i<n;i++)for(int j=i;j<n;j++){
      int shared=i&j,factor=(i==j?1:2);
      for(int k=stage+1;k<4;k++)if(shared&(1<<(k-stage-1)))factor*=rad[k];
      Poly even=mul(current[2*i],current[2*j]);
      Poly odd=mul(current[2*i+1],current[2*j+1]);
      Poly term=add(even,scale(odd,rad[stage]),-1);
      term=scale(term,factor);
      next[i^j]=add(next[i^j],term);
   }
   current.swap(next);
   cerr<<"Degree now "<<current[0].size()-1<<", max coefficient digits approx "<<bits(current[0][0])*0.302<<"\n";
 }
 if(current.size()!=1||current[0].size()!=1793)throw runtime_error("Output degree not 1792");
 Poly& P=current[0];Z content=0;
 for(const auto&x:P)mpz_gcd(content.get_mpz_t(),content.get_mpz_t(),x.get_mpz_t());
 if(content==0)throw runtime_error("Zero norm");
 if(P.back()<0)content=-content;
 for(auto&x:P){mpz_divexact(x.get_mpz_t(),x.get_mpz_t(),content.get_mpz_t());}
 ofstream out(argv[2]);if(!out)throw runtime_error("Cannot write result");
 out<<"power\tcoefficient\n";
 for(size_t i=0;i<P.size();i++)out<<i<<'\t'<<P[i]<<'\n';
 cerr<<"DONE primitive 1792, leading coefficient digits "<<P.back().get_str().size()<<", common content digits "<<content.get_str().size()<<"\n";
}
