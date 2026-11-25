#include <algorithm>
#include <bit>
#include <charconv>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <map>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>
#include <string>
using namespace std;
using U=uint32_t; using Perm=vector<int>;
static constexpr int MAXN=30;
struct Result {int cost; Perm witness;};
struct Solver {
 int n; U pred[MAXN+1][MAXN]{}; U chain[MAXN+1][MAXN]{}; U packed[MAXN+1][MAXN][MAXN+1]{};
 Solver(int n):n(n){for(int h=1;h<n;h++)for(int r=0;r<h;r++){U m=0;int k=0;for(int i=r;i<n;i+=h){pred[h][i]=m;m|=U(1)<<i;packed[h][r][++k]=m;}chain[h][r]=m;}}
 U pass(U s,int h) const { U t=0; for(int r=0;r<h;r++)t|=packed[h][r][std::popcount(s&chain[h][r])];return t; }
 int exec(const Perm& input,const vector<int>& H) const {int a[MAXN];copy(input.begin(),input.end(),a);int c=0;for(int h:H)for(int i=h;i<n;i++){int x=a[i],j=i;while(j>=h){++c;if(a[j-h]<x)break;a[j]=a[j-h];j-=h;}a[j]=x;}return c;}
 int firstcost(int h) const{int c=0;for(int i=h;i<n;i++)c+=i/h;return c;}
 Result exact(const vector<int>& H) const {
  int h=H[0]; if(H.size()==1){Perm w(n);iota(w.rbegin(),w.rend(),0);return {firstcost(h),w};}
  // Mixed-radix states: digit r is the number of smallest ranks on the r-th h-chain.
  int stride[MAXN],radix[MAXN];int M=1;for(int r=0;r<h;r++){stride[r]=M;radix[r]=std::popcount(chain[h][r])+1;M*=radix[r];}
  vector<U> s(M); for(int r=0;r<h;r++)for(int k=1;k<radix[r];k++)for(int j=0;j<stride[r];j++)s[k*stride[r]+j]=s[j]|packed[h][r][k];
  int p=(int)H.size()-1;vector<vector<U>> images(p);images[0]=move(s);for(int i=1;i<p;i++){images[i].resize(M);for(int j=0;j<M;j++)images[i][j]=pass(images[i-1][j],H[i]);}
  int prevlen[MAXN+1][MAXN];for(int g:H)for(int i=0;i<n;i++)prevlen[g][i]=i/g;
  vector<int> dp(M,-1);vector<unsigned char> parent(M,255);dp[0]=0;
  // Forward mixed-radix enumeration: every increment reaches a larger integer.
  int digit[MAXN]{};
  for(int j=0;j<M-1;j++){
   for(int r=0;r<h;r++)if(digit[r]+1<radix[r]){
    int next=j+stride[r],cost=dp[j];
    for(int i=0;i<p;i++) {U a=images[i][j],b=images[i][next];U diff=b^a;assert(diff && !(diff&(diff-1)) && !(a&diff));int pos=std::countr_zero(diff),g=H[i+1];int small=std::popcount(a&pred[g][pos]);cost+=prevlen[g][pos]-small+(small!=0);}
    if(cost>dp[next]){dp[next]=cost;parent[next]=r;}
   }
   for(int r=0;r<h;r++){if(++digit[r]<radix[r])break;digit[r]=0;}
  }
  Perm w(n,-1);int j=M-1;
  for(int rank=n-1;rank>=0;rank--){int r=parent[j],prev=j-stride[r];int pos=std::countr_zero(images[0][j]^images[0][prev]);w[pos]=rank;j=prev;}
  for(int r=0;r<h;r++){int last=r+((n-1-r)/h)*h;for(int a=r,b=last;a<b;a+=h,b-=h)swap(w[a],w[b]);}
  int answer=firstcost(h)+dp.back();if(exec(w,H)!=answer)throw runtime_error("witness mismatch");return {answer,w};
 }
};
vector<int> gaps(U bits,int n){vector<int> H;for(int g=n-1;g>=2;g--)if(bits&(U(1)<<(g-2)))H.push_back(g);H.push_back(1);return H;}
string show(const vector<int>& H){string s;for(int x:H){if(!s.empty())s+=",";s+=to_string(x);}return s;}
// Fixed initial candidates. The exact DP, not the published guesses, certifies their upper bound.
vector<int> seed(int n){if(n<=5)return {1};if(n==6)return {4,1};if(n==7)return {6,4,1};if(n==8)return {7,5,1};if(n==9)return {8,5,1};if(n==10)return {9,6,1};if(n==11)return {10,9,6,1};if(n==12)return {11,10,7,1};if(n==13)return {10,6,1};if(n==14)return {13,11,7,1};if(n==15)return {14,9,4,1};if(n==16)return {9,7,4,1};if(n==17)return {9,6,4,1};if(n==18)return {17,9,6,4,1};if(n==20)return {11,7,5,1};if(n==25)return {24,9,7,4,1};if(n>=19)return {9,7,4,1};return {1};}
int number(const string& text) {
 int value{};
 auto result = from_chars(text.data(), text.data()+text.size(), value);
 if(result.ec != errc{} || result.ptr != text.data()+text.size()) throw invalid_argument("expected integer: "+text);
 return value;
}
int main(int argc,char**argv){
 if(argc >= 3) {
  const string mode=argv[2];
  if(!((mode=="cert" && argc==4) || (mode=="ties" && argc==3) || (mode=="exact" && argc>=4))) {
   cerr<<"usage: minimax n [ties | cert file | exact gaps...]\n"; return 1;
  }
 }
 if(argc<2){cerr<<"usage: minimax n [ties] [exact-only gaps...]\n";return 1;}int n=number(argv[1]);if(n<2||n>MAXN)throw runtime_error("n out of range");Solver s(n);
 if(argc>=3 && string(argv[2])=="exact"){vector<int> H;for(int i=3;i<argc;i++)H.push_back(number(argv[i]));if(H.empty()||H.back()!=1||H.front()>=n)throw runtime_error("illegal gaps");for(size_t i=1;i<H.size();i++)if(H[i]>=H[i-1])throw runtime_error("illegal gaps");auto r=s.exact(H);cout<<"n="<<n<<" gaps="<<show(H)<<" max="<<r.cost<<" witness="<<show(r.witness)<<"\n";return 0;}
 bool cert=argc>=4&&string(argv[2])=="cert"; bool ties=cert||(argc>=3&&string(argv[2])=="ties");auto start=chrono::steady_clock::now();auto H=seed(n);auto init=s.exact(H);int best=init.cost;vector<vector<int>> winners; if(!ties)winners.push_back(H);vector<Perm> pool{init.witness};Perm w(n);iota(w.begin(),w.end(),0);reverse(w.begin(),w.end());pool.push_back(w);
 // A deterministic witness sieve. Each rejection is justified by an actual execution.
 mt19937 rng(20261125);for(int i=0;i<32;i++){shuffle(w.begin(),w.end(),rng);pool.push_back(w);}int sieve=0,base=0,full=0; ofstream cf; map<Perm,int> ids; if(cert){cf.open(argv[3]); if(!cf)throw runtime_error("cannot open certificate"); cf<<"N "<<n<<" "<<best<<"\n";} auto emitWitness=[&](U bits,const Perm& w){if(!cert)return; auto [it,isNew]=ids.try_emplace(w,(int)ids.size()); if(isNew){cf<<"P "<<it->second; for(auto x:w)cf<<" "<<x; cf<<"\n";} cf<<"X "<<bits<<" "<<it->second<<"\n";};U total=U(1)<<(n-2);cout<<"initial n="<<n<<" best="<<best<<" gaps="<<show(H)<<"\n"<<flush;
 for(U bits=0;bits<total;bits++){
  H=gaps(bits,n);int b=0;for(int g:H)b+=n-g;
  auto reject=[&](int value){return ties?value>best:value>=best;};
  if(reject(b)){base++;if(cert)cf<<"B "<<bits<<"\n";continue;}
  bool bad=false;for(size_t i=0;i<pool.size();i++)if(reject(s.exec(pool[i],H))){emitWitness(bits,pool[i]);swap(pool[0],pool[i]);bad=true;break;}if(bad){sieve++;continue;}
  auto r=s.exact(H);full++;pool.insert(pool.begin(),r.witness);
  if(cert){if(r.cost<best)throw runtime_error("seed not optimal: restart with improved seed");if(r.cost==best)cf<<"O "<<bits<<"\n";else emitWitness(bits,r.witness);} if(r.cost<best){best=r.cost;winners={H};cout<<"improved "<<best<<" gaps="<<show(H)<<" mask="<<bits<<" full="<<full<<"\n"<<flush;}else if(ties&&r.cost==best)winners.push_back(H);
  if(full%100==0)cerr<<"progress n="<<n<<" mask="<<bits<<" full="<<full<<" pool="<<pool.size()<<"\n";
 }
 cout<<"FINAL n="<<n<<" min="<<best<<" schedules="<<total<<" baseline_pruned="<<base<<" witness_pruned="<<sieve<<" dp="<<full<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";for(auto& h:winners)cout<<"winner "<<show(h)<<"\n";
 if(cert){cf<<"END "<<total<<"\n";cf.close();if(!cf)throw runtime_error("certificate write failed");} if(base+sieve+full!=total)throw runtime_error("incomplete coverage");
}
