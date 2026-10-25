// Single-thread modular evaluator for full permutation sums of two-root forest kernels.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <vector>
#include <tuple>
using namespace std; constexpr uint32_t P=1000003;
uint32_t mul(uint64_t a,uint64_t b){return a*b%P;}uint32_t power(uint32_t a,uint32_t n){uint32_t r=1;while(n){if(n&1)r=mul(r,a);a=mul(a,a);n>>=1;}return r;}
int main(int argc,char**argv){if(argc!=4)return 2;ifstream in(argv[1],ios::binary);uint32_t counts[3];in.read((char*)counts,12);auto[nunits,nfactors,nstates]=tuple{counts[0],counts[1],counts[2]};vector<uint32_t>fac(3*nfactors),starts(nunits+1),states(7*nstates);in.read((char*)fac.data(),fac.size()*4);in.read((char*)starts.data(),starts.size()*4);in.read((char*)states.data(),states.size()*4);ifstream points(argv[2]);int nrows,n;points>>nrows>>n;if(n!=7)return 3;ofstream out(argv[3],ios::binary);vector<uint32_t>den(nfactors),prefix(nfactors+1),inv(nfactors),result(nunits);for(int row=0;row<nrows;row++){int64_t sums[128]={0},omega[7];for(auto &x:omega)points>>x;for(int mask=1;mask<128;mask++){int bit=__builtin_ctz(mask);sums[mask]=sums[mask^(1<<bit)]+omega[bit];}prefix[0]=1;for(int j=0;j<(int)nfactors;j++){int64_t a=sums[fac[3*j]],q=sums[fac[3*j+1]],sgn=fac[3*j+2]?1:-1;int64_t x=q%P,y=(q+sgn*a)%P;if(x<0)x+=P;if(y<0)y+=P;den[j]=mul(x,y);if(!den[j]){cerr<<"pole "<<row<<" "<<j<<endl;return 4;}prefix[j+1]=mul(prefix[j],den[j]);}uint32_t total=power(prefix[nfactors],P-2);for(int j=nfactors-1;j>=0;j--){inv[j]=mul(total,prefix[j]);total=mul(total,den[j]);}for(int u=0;u<(int)nunits;u++){uint32_t answer=0;for(uint32_t j=starts[u];j<starts[u+1];j++){uint32_t*st=&states[7*j];int64_t a=-sums[st[0]]%P;if(a<0)a+=P;uint32_t term=mul(mul(a,a),a);for(int k=1;k<=5;k++)term=mul(term,inv[st[k]]);term=mul(term,st[6]);answer+=term;if(answer>=P)answer-=P;}result[u]=answer;}out.write((char*)result.data(),result.size()*4);}cerr<<"evaluated "<<nrows<<" rows; "<<nunits<<" columns; "<<nstates<<" distinct monomials\n";}
