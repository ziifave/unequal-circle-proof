#include <algorithm>
#include <gmpxx.h>
#include <array>
#include <vector>
#include <stdexcept>
#include <iostream>
#include <fstream>
#include <string>
#include <chrono>
using namespace std;
struct K {
 array<mpq_class,16> c;
 K(long v=0){c[0]=v;}
 bool zero() const {for(const auto&z:c) if(z!=0)return false;return true;}
 K operator-()const{K a;for(int i=0;i<16;i++)a.c[i]=-c[i];return a;}
 K operator+(const K&b)const{K a;for(int i=0;i<16;i++)a.c[i]=c[i]+b.c[i];return a;}
 K operator-(const K&b)const{K a;for(int i=0;i<16;i++)a.c[i]=c[i]-b.c[i];return a;}
 K operator*(const K&b)const{
   K a;const int ns[4]={2,3,5,7};
   for(int i=0;i<16;i++)if(c[i]!=0)for(int j=0;j<16;j++)if(b.c[j]!=0){
      int mask=i&j,v=1;for(int k=0;k<4;k++)if(mask&(1<<k))v*=ns[k];
      a.c[i^j]+=v*c[i]*b.c[j];
   }return a;
 }
 K operator*(const mpq_class&b)const{K a;for(int i=0;i<16;i++)a.c[i]=c[i]*b;return a;}
 K operator/(const mpq_class&b)const{K a;for(int i=0;i<16;i++)a.c[i]=c[i]/b;return a;}
 K conj(int i)const{K a;for(int j=0;j<16;j++)a.c[j]=(j&(1<<i))?-c[j]:c[j];return a;}
 K inv()const{
   if(zero())throw runtime_error("division by 0");K b=*this,adj(1);
   for(int i=0;i<4;i++){K cp=b.conj(i);adj=adj*cp;b=b*cp;}
   for(int i=1;i<16;i++)if(b.c[i]!=0)throw runtime_error("inverse not rational");
   return adj/b.c[0];
 }
 K sq()const{return (*this)*(*this);}
};
K operator*(long b,const K&a){return a*mpq_class(b);}
using V=vector<K>;
void trim(V&a){while(a.size()>1&&a.back().zero())a.pop_back();}
V add(V a,const V&b){if(a.size()<b.size())a.resize(b.size());for(size_t i=0;i<b.size();i++)a[i]=a[i]+b[i];trim(a);return a;}
V neg(V a){for(auto&x:a)x=-x;return a;}
V sub(V a,const V&b){return add(a,neg(b));}
V scale(V a,const K&k){for(auto&x:a)x=x*k;trim(a);return a;}
V mul(const V&a,const V&b){V c(a.size()+b.size()-1);for(size_t i=0;i<a.size();i++)if(!a[i].zero())for(size_t j=0;j<b.size();j++)if(!b[j].zero())c[i+j]=c[i+j]+a[i]*b[j];trim(c);return c;}
V det4(const vector<vector<V>>&mat){
   int p[4]={0,1,2,3};V out={K(0)};
   do{
      int inv=0;V v={K(1)};
      for(int i=0;i<4;i++){for(int j=i+1;j<4;j++) if(p[i]>p[j])inv++;v=mul(v,mat[i][p[i]]);}
      out=add(out,scale(v,K(inv%2?-1:1)));
   }while(next_permutation(p,p+4));return out;
}
K determinant(vector<V> mat){
 int n=mat.size();K sign(1),last(1);
 for(int k=0;k<n-1;k++){
   int ix=k;while(ix<n&&mat[ix][k].zero())ix++;
   if(ix==n)return K(0);
   if(ix!=k){swap(mat[ix],mat[k]);sign=-sign;}
   K pivot=mat[k][k];K ilast=last.inv();
   for(int i=k+1;i<n;i++){
     for(int j=k+1;j<n;j++)mat[i][j]=(mat[i][j]*pivot-mat[i][k]*mat[k][j])*ilast;
     mat[i][k]=K(0);
   }
   last=pivot;
 }
 return sign*mat[n-1][n-1];
}
K resultant(const V&a,const V&b){
   const int n=a.size()-1,m=b.size()-1;int siz=n+m;
   vector<V> mat(siz,V(siz,K(0)));
   for(int row=0;row<m;row++)for(int j=0;j<=n;j++)mat[row][row+j]=a[j];
   for(int row=0;row<n;row++)for(int j=0;j<=m;j++)mat[m+row][row+j]=b[j];
   return determinant(mat);
}
K rad(int i){
 K a; switch(i){case 2:a.c[1]=1;break;case 3:a.c[2]=1;break;case 5:a.c[4]=1;break;case 7:a.c[8]=1;break;case 6:a.c[3]=1;break;case 8:a.c[1]=2;break;case 9:a.c[0]=3;break;case 10:a.c[5]=1;break;default:throw runtime_error("radius");}
 return a;
}
K r2=rad(2),r5=rad(5),r6=rad(6),r7=rad(7),r8=rad(8),r9=rad(9),r10=rad(10);
K d=r5+r7,b=r7+r10,aa=r5+r10,id=(r7-r5)/mpq_class(2),lam=(b.sq()+d.sq()-aa.sq())*id.sq()/mpq_class(2),kap=4L*r5*r7*r10*(r5+r7+r10)*id.sq().sq();
K radius(int i){switch(i){case 2:return r2;case 5:return r5;case 6:return r6;case 7:return r7;case 8:return r8;case 9:return r9;case 10:return r10;default:throw runtime_error("invalid radius");}}
struct ND{K N,D;};
K evaluate(long x){
 K R(x);K t5=R-r5,t6=R-r6,t7=R-r7;
 auto nd=[&](int i,int j){K dd=(R-radius(i))*(R-radius(j));return ND{dd-2L*radius(i)*radius(j),dd};};
 auto c1=nd(7,9),c2=nd(9,2),c3=nd(2,8),c4=nd(8,6);
 auto N1=c1.N,D1=c1.D,N2=c2.N,D2=c2.D;
 V P2={D2.sq()*N1.sq()+D1.sq()*N2.sq()-D1.sq()*D2.sq(),-2L*N1*D1*N2*D2,D1.sq()*D2.sq()};
 K c=P2[0],bb=P2[1],at=P2[2],N=c3.N,D=c3.D,A=D.sq();
 V B={K(0),-2L*N*D},C0={N.sq()-D.sq(),K(0),D.sq()};
 V L=sub(scale(B,at),{A*bb}),T=sub(scale(C0,at),{A*c});
 V P3=scale(add(sub(scale(mul(L,L),c),scale(mul(L,T),bb)),scale(mul(T,T),at)),at.inv());
 if(P3.size()!=5)throw runtime_error("deg3");
 K a3=P3.back(); K inv3=a3.inv();
 V pmonic=scale(P3,inv3);
 N=c4.N;D=c4.D;A=D.sq();
 vector<V>M(4,V(4));for(int j=0;j<3;j++)M[j+1][j]=K(1);
 for(int j=0;j<4;j++)M[j][3]=-pmonic[j];
 vector<V>M2(4,V(4));for(int i=0;i<4;i++)for(int j=0;j<4;j++)for(int k=0;k<4;k++)M2[i][j]=M2[i][j]+M[i][k]*M[k][j];
 vector<vector<V>>Q(4,vector<V>(4));
 for(int i=0;i<4;i++)for(int j=0;j<4;j++){
   Q[i][j]={A*M2[i][j]+(i==j?N.sq()-A:K(0)),-2L*N*D*M[i][j],i==j?A:K(0)};
 }
 V P4=scale(det4(Q),a3.sq());if(P4.size()!=9)throw runtime_error("deg4");
 auto c57=nd(5,7);K N57=c57.N,D57=c57.D;
 K q=t5*N57-t7*D57,J=D57.sq()-N57.sq();
 K B0=t6.sq()+t7.sq()+b.sq()-(r6+r10).sq();
 V Ap=add(scale({B0,-2L*t6*t7},D57),scale({t7,-t6},2L*lam*q));
 V diff={-t7,t6},W={K(1),K(0),K(-1)};
 V Ep=add(mul(Ap,Ap),scale(W,4L*t6.sq()*kap*q.sq()));
 V Ip=add(scale(mul(diff,diff),4L*kap*t5.sq()),scale(W,4L*t6.sq()*lam.sq()*t5.sq()));
 Ep=sub(Ep,scale(Ip,J));
 V Th=sub(scale(Ap,q),scale(diff,2L*J*lam*t5.sq()));
 V H=sub(mul(Ep,Ep),scale(mul(W,mul(Th,Th)),16L*kap*t6.sq()));
 if(H.size()!=5)throw runtime_error("degH");
 return resultant(P4,H);
}
K kpow(K a,int n){K b(1);while(n){if(n&1)b=b*a;a=a*a;n>>=1;}return b;}
K evalG(long x){
  K y=evaluate(x);
  for(int i: {2,5,6,7,8,9}){
    y=y*kpow((K(x)+radius(i))/mpq_class(x*x-i),32);
  }
  y=y*kpow((K(x)-r10)/mpq_class(x*x-10),16);
  return y;
}
int main(int argc,char**argv){
 if(argc>=2&&string(argv[1])=="probe"){
  for(int x=0;x<3;x++){auto st=chrono::steady_clock::now();K y=evaluate(x);cerr<<"x="<<x<<" time="<<chrono::duration<double>(chrono::steady_clock::now()-st).count()<<" result0="<<y.c[0].get_str().substr(0,70)<<"\n";}
  return 0;
 }
 if(argc!=2){cerr<<"Usage: exact_G112 <output.tsv>\n"; return 2;}
 cerr<<"Computing 113 exact quotient values in K at integer R=0..113 skipping 3\n";
 vector<long> xs;for(long i=0;i<=113;i++)if(i!=3)xs.push_back(i);
 if(xs.size()!=113)throw runtime_error("nodes not 113");
 vector<K> vals(113);auto start=chrono::steady_clock::now();
 #pragma omp parallel for schedule(dynamic,1) num_threads(4)
 for(int i=0;i<113;i++){
  vals[i]=evalG(xs[i]);
  if(i%8==0)cerr<<"evaluated index "<<i+1<<" / 113 in "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"s\n";
 }
 vector<K> delta=vals;
 for(int j=1;j<=112;j++)for(int i=112;i>=j;i--)delta[i]=(delta[i]-delta[i-1])/mpq_class(xs[i]-xs[i-j]);
 vector<K> coeffs(113),basis={K(1)};
 for(int j=0;j<=112;j++){
  for(size_t k=0;k<basis.size();k++) coeffs[k]=coeffs[k]+delta[j]*basis[k];
  if(j<112){vector<K> bn(basis.size()+1);for(size_t k=0;k<basis.size();k++){
    bn[k]=bn[k]-basis[k]*mpq_class(xs[j]);bn[k+1]=bn[k+1]+basis[k];
   }basis=move(bn);}
 }
 cerr<<"interpolated polynomial in characteristic zero; validating held-out evaluations\n";
 for(int x: {114,115,116}){
  K ev(0);for(int j=112;j>=0;j--)ev=ev*K(x)+coeffs[j];
  if(!(ev-evalG(x)).zero()){cerr<<"FAILED polynomial interpolation at x="<<x<<"\n";return 1;}
 }
 cerr<<"Held-out evaluations passed. Quotient degree112? "<<(!coeffs[112].zero())<<"\n";
 K topinv=coeffs.back().inv();for(K&v:coeffs)v=v*topinv;
 if(coeffs.back().c[0]!=1)throw runtime_error("not monic");
 cerr<<"ALL EXACT CHARACTERISTIC-ZERO COEFFICIENTS EXTRACTED\n";
 ofstream fout(argv[1]);
 fout<<"power";for(int mask=0;mask<16;mask++)fout<<"\tbasis_"<<mask;fout<<"\n";
 for(int i=0;i<=112;i++){
  fout<<i;for(int mask=0;mask<16;mask++)fout<<"\t"<<coeffs[i].c[mask].get_str();fout<<"\n";
 }
 cerr<<"Output: "<<argv[1]<<"\n";
 return 0;
}
