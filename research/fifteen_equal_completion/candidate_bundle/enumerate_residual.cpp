#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <numeric>
#include <algorithm>
using namespace std;
constexpr int Q[12][12]={
  {0, 8700, 8700, 6746, 6142, 5883, 4896, 4047, 0, 0, 0, 0},
  {8700, 8700, 5105, 4784, 4585, 4488, 4077, 3690, 3228, 2344, 1738, 0},
  {8700, 5105, 4086, 3923, 3818, 3767, 3541, 3321, 3105, 2889, 2720, 0},
  {6746, 4784, 3923, 3780, 3688, 3642, 3442, 3245, 3051, 2856, 2744, 0},
  {6142, 4585, 3818, 3688, 3603, 3561, 3376, 3194, 3014, 2832, 2727, 656},
  {5883, 4488, 3767, 3642, 3561, 3521, 3344, 3169, 2994, 2819, 2717, 868},
  {4896, 4077, 3541, 3442, 3376, 3344, 3198, 3051, 2904, 2754, 2668, 950},
  {4047, 3690, 3321, 3245, 3194, 3169, 3051, 2932, 2809, 2682, 2609, 1214},
  {0, 3228, 3105, 3051, 3014, 2994, 2904, 2809, 2709, 2604, 2541, 1383},
  {0, 2344, 2889, 2856, 2832, 2819, 2754, 2682, 2604, 2518, 2467, 1499},
  {0, 1738, 2720, 2744, 2727, 2717, 2668, 2609, 2541, 2467, 2422, 1579},
  {0, 0, 0, 0, 656, 868, 950, 1214, 1383, 1499, 1579, 1612},
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
    const int q=(label[i]==12||label[j]==12)?0:Q[label[i]][label[j]];
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
      r.witness+=",";
    }else r.cyclic++;
    return;
  }
  int p=innerpos[depth];
  for(int t=0;t<11;t++){
    label[p]=t;
    rec(depth+1,small+(t<=1),high+(t>=5),high2+(t>=8),r);

  }
  label[p]=12;
}
int main(int argc,char**argv){
 int maxk= argc>=2?stoi(argv[1]):5;
 ifstream in("stage3.tsv");string a,b,rep,status;
 array<int,9>total{},newClosed{},still{};
 string line;
 while(getline(in,line)){
   size_t pos=line.find('\t');
   if(pos==string::npos || line.substr(0,pos)!="UNKNOWN")continue;
   size_t x=line.find('\t',pos+1),y=line.find('\t',x+1);
   if(x==string::npos || y==string::npos)continue;
   b=line.substr(pos+1,x-pos-1); rep=line.substr(x+1,y-x-1); status=line.substr(y+1);
   int k=stoi(b);
   if(k>maxk)continue;
   nInner=k;innerpos.clear();label.fill(11);
   for(int i=0;i<N;i++)if(rep[i]=='1'){innerpos.push_back(i);label[i]=12;}
   Result r;rec(0,0,0,0,r);
   total[k]++;
   if(r.any){still[k]++;cout<<"UNKNOWN\t"<<k<<"\t"<<rep<<"\t"<<r.viable<<"\t"<<r.boxes<<"\t"<<r.witness<<"\n";}
   else{newClosed[k]++;cout<<"CLOSED\t"<<k<<"\t"<<rep<<"\t"<<r.boxes<<"\n";}
 }
 for(int k=5;k<=maxk;k++)cerr<<"k="<<k<<" total="<<total[k]<<" CLOSED="<<newClosed[k]<<" UNKNOWN="<<still[k]<<"\n";
}
