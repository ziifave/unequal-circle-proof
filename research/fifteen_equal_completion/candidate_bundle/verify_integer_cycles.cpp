// Standalone second-stage rigorous finite enumerator for 15 equal disks.
// Compile: g++ -O3 -std=c++17 verify_integer_cycles.cpp -o verify_integer_cycles
// Run: ./verify_integer_cycles
// Uses only exact bounded integers (no float, no external dependencies).
// Audited route: tests every one of the 760 dihedral words; no word is skipped
// by the separate analytic gap-capacity filter.
#include <array>
#include <vector>
#include <string>
#include <set>
#include <iostream>
#include <iomanip>
#include <cassert>
using namespace std;
static constexpr int N=15, TWO_PI_UP=17600;
// radians * 2800; all are strict rational lower bounds
static constexpr int Q[4][4]={
  /*  O    S     M     H */
  {1610, 0,    0,   840},  // O
  {0,    0,    0,   0},  // S, center norm < 1 (at most one)
  {0,    0, 3360, 2408},  // M, 1<= norm <5/3
  {840,  0, 2408, 2408}   // H, 5/3<= norm <L
};

static string canon(string s) {
 string best(15,'2');
 for(int flip=0;flip<2;flip++){
   string t=s;
   if(flip) {t=string(s.rbegin(),s.rend());}
   for(int j=0;j<15;j++){
     string r=t.substr(j)+t.substr(0,j);
     if(r<best)best=r;
   }
 }
 return best;
}
static vector<int> innerRuns(const string &s){
 int start=0;
 while(s[start]=='1')start++;
 vector<int> runs; int r=0;
 for(int i=1;i<=15;i++){
   char c=s[(start+i)%15];
   if(c=='1')r++;
   else if(r){runs.push_back(r);r=0;}
 }
 if(r)runs.push_back(r);
 return runs;
}
// Truth means the given rational necessary constraints admit an angular assignment.
// False means a negative cycle and hence this radial-type assignment is impossible.
static bool noNegativeCycle(const array<int,15> &labels){
 array<int,15> d{};
 for(int it=0;it<15;it++){
   bool change=false;
   for(int i=0;i<14;i++){
     if(d[i]>d[i+1]){d[i]=d[i+1];change=true;}
   }
   for(int i=0;i<15;i++)for(int j=i+1;j<15;j++){
     const int q=Q[labels[i]][labels[j]];
     // theta_j-theta_i >= q/2800
     if(d[i]>d[j]-q){d[i]=d[j]-q;change=true;}
     // theta_j-theta_i <= 2*pi - q/2800
     // 2*pi < 44/7 = 17600/2800.
     if(d[j]>d[i]+TWO_PI_UP-q){d[j]=d[i]+TWO_PI_UP-q;change=true;}
   }
   if(!change)return true;
 }
 return false; // Bellman-Ford negative cycle
}
static bool allTypesNegativeRec(const vector<int>& positions, int k, int depth,
                                int nsmall, int nhigh, array<int,15> &lab){
 if(nsmall>1)return true;
 if(nhigh+(k-depth)<k-4)return true;
 if(depth==k){
   if(nhigh<k-4)return true;
   return !noNegativeCycle(lab);
 }
 for(int type=1;type<=3;type++){
   lab[positions[depth]]=type;
   if(!allTypesNegativeRec(positions,k,depth+1,nsmall+(type==1),nhigh+(type==3),lab)){
     lab[positions[depth]]=0;return false;
   }
 }
 lab[positions[depth]]=0;return true;
}
static bool allTypesNegative(const string &rep,int k){
 vector<int> pos;
 for(int i=0;i<15;i++)if(rep[i]=='1')pos.push_back(i);
 assert((int)pos.size()==k);
 array<int,15> labels{};
 return allTypesNegativeRec(pos,k,0,0,0,labels);
}
int main(int argc, char** argv){
 bool emit=(argc>1 && string(argv[1])=="--list");
 int totalAll=0,totalAnalytic=0,totalGraph=0,totalUnknown=0;
 for(int k=5;k<=8;k++){
   set<string> orbits;
   for(int mask=0;mask<(1<<15);mask++){
     if(__builtin_popcount((unsigned)mask)!=k)continue;
     string s(15,'0');
     for(int i=0;i<15;i++)if(mask & (1<<i))s[i]='1';
     orbits.insert(canon(s));
   }
   int analytic=0,graph=0,unknown=0;
   for(const auto &rep:orbits){
     // Do not rely on a combinatorial gap filter: apply the certified integer
     // angular graph to every orbit class directly.
     bool excludedAnalytic=false;
     if(allTypesNegative(rep,k)){graph++;if(emit)cout<<"orbit\t"<<k<<"\t"<<rep<<"\tNEGATIVE_CYCLE\n";}
     else{unknown++;if(emit)cout<<"orbit\t"<<k<<"\t"<<rep<<"\tUNKNOWN\n";}
   }
   totalAll+=orbits.size();totalAnalytic+=analytic;totalGraph+=graph;totalUnknown+=unknown;
   cout<<"inner="<<k<<" outer="<<(15-k)<<" total="<<orbits.size()
       <<" analytic="<<analytic<<" graph="<<graph<<" UNKNOWN="<<unknown<<"\n";
 }
 cout<<"TOTAL "<<totalAll<<" = analytic "<<totalAnalytic
     <<" + graph "<<totalGraph<<" + UNKNOWN "<<totalUnknown<<"\n";
 assert(totalAll==760 && totalAnalytic==0 && totalGraph==382 && totalUnknown==378);
 return 0;
}
