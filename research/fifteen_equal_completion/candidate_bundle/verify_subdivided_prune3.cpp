#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <numeric>
#include <algorithm>
using namespace std;
constexpr int Q[8][8]={
  {0, 8700, 8700, 6746, 6142, 4047, 0, 0},
  {8700, 8700, 5105, 4784, 4585, 3690, 1738, 0},
  {8700, 5105, 4086, 3923, 3818, 3321, 2720, 0},
  {6746, 4784, 3923, 3780, 3688, 3245, 2744, 0},
  {6142, 4585, 3818, 3688, 3603, 3194, 2727, 656},
  {4047, 3690, 3321, 3245, 3194, 2932, 2609, 868},
  {0, 1738, 2720, 2744, 2727, 2609, 2422, 1383},
  {0, 0, 0, 0, 656, 868, 1383, 1612},
};
constexpr int N=15, TWOPI=17600;
struct Edge {int u,v,w;};
struct Result {long long boxes=0, viable=0, cyclic=0, countmismatch=0; bool any=false; string witness="";};
array<int,N> label;
vector<int> innerpos;
int nInner;
long long tests=0;
static bool noNeg(){
  // Standard necessary angular difference inequalities, enhanced with ordering.
  Edge e[255];int ne=0;
  for(int i=0;i<N-1;i++)e[ne++]={i+1,i,0};
  for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){
    const int q=(label[i]==8||label[j]==8)?0:Q[label[i]][label[j]];
    e[ne++]={j,i,-q};e[ne++]={i,j,TWOPI-q};
  }
  int d[N]={};
  for(int k=0;k<N;k++){
    bool ch=false;
    for(int p=0;p<ne;p++){
      const Edge &z=e[p];
      if(d[z.v]>d[z.u]+z.w){d[z.v]=d[z.u]+z.w;ch=true;}
    }
    if(!ch)return true;
  }
  return false;
}
void rec(int depth,int small,int high,int high2,Result& r){
  if(r.any)return;
  if(small>1||high+(nInner-depth)<nInner-4||high2+(nInner-depth)<max(0,nInner-5))return;
  if(small==1){
    // if the unique small center is in [0,0.5), no circle in [1,1.5) can coexist.
    bool zero=false,mone=false;
    for(int i=0;i<N;i++){zero |= label[i]==0;mone |= label[i]==2;}
    if(zero && mone)return;
  }
  if(depth>=3 && !noNeg()){r.cyclic++;return;}
  if(depth==nInner){
    r.boxes++;
    if(noNeg()){
      r.viable++;r.any=true;
      for(int j=0;j<nInner;j++)r.witness+=char('0'+label[innerpos[j]]);
    }else r.cyclic++;
    return;
  }
  int p=innerpos[depth];
  for(int t=0;t<7;t++){
    label[p]=t;
    rec(depth+1,small+(t<=1),high+(t>=5),high2+(t>=6),r);
    if(r.any)break;
  }
  label[p]=8;
}
int main(int argc,char**argv){
 int maxk= argc>=2?stoi(argv[1]):5;
 ifstream in("verified_orbits.tsv");string a,b,rep,status;
 array<int,9>total{},newClosed{},still{};
 string line;
 while(getline(in,line)){
   size_t pos=line.find('\t');
   if(pos==string::npos || line.substr(0,pos)!="orbit")continue;
   size_t x=line.find('\t',pos+1),y=line.find('\t',x+1);
   if(x==string::npos || y==string::npos)continue;
   b=line.substr(pos+1,x-pos-1); rep=line.substr(x+1,y-x-1); status=line.substr(y+1);
   int k=stoi(b);
   if(status!="UNKNOWN"||k>maxk)continue;
   nInner=k;innerpos.clear();label.fill(7);
   for(int i=0;i<N;i++)if(rep[i]=='1'){innerpos.push_back(i);label[i]=8;}
   Result r;rec(0,0,0,0,r);
   total[k]++;
   if(r.any){still[k]++;cout<<"UNKNOWN\t"<<k<<"\t"<<rep<<"\t"<<r.witness<<"\t"<<r.boxes<<"\n";}
   else{newClosed[k]++;cout<<"CLOSED\t"<<k<<"\t"<<rep<<"\t"<<r.boxes<<"\n";}
 }
 for(int k=5;k<=maxk;k++)cerr<<"k="<<k<<" total="<<total[k]<<" CLOSED="<<newClosed[k]<<" UNKNOWN="<<still[k]<<"\n";
}
