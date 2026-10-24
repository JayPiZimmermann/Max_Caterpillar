#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
constexpr uint64_t P=1000000007ULL;
uint32_t mul(uint64_t a,uint64_t b){return a*b%P;}
uint32_t power(uint32_t a,uint64_t k){uint32_t r=1;for(;k;k>>=1,a=mul(a,a))if(k&1)r=mul(r,a);return r;}
uint32_t mod(int64_t x){x%=int64_t(P);return x<0?x+P:x;}
template<class T>vector<T>read(ifstream&f,size_t n){vector<T>x(n);f.read((char*)x.data(),n*sizeof(T));if(!f)throw runtime_error("short input");return x;}
int main(int argc,char**argv){try{
 if(argc!=4)throw runtime_error("usage DAG POINTS OUTPUT");
 ifstream f(argv[1],ios::binary);auto h=read<uint64_t>(f,6);if(h[0]!=0x5557504154483031ULL)throw runtime_error("magic");
 size_t n=h[1],ns=h[2],nt=h[3],nc=h[4],nf=h[5],m=n-1;
 auto starts=read<uint32_t>(f,ns+1),left=read<uint32_t>(f,nt),factor=read<uint32_t>(f,nt),roots=read<uint32_t>(f,nc),masks=read<uint32_t>(f,nf);
 auto heads=read<int32_t>(f,nf);auto weights=read<uint32_t>(f,nf);
 ifstream points(argv[2]);size_t nr,nn;points>>nr>>nn;if(nn!=n)throw runtime_error("arity");ofstream out(argv[3],ios::binary);
 vector<int64_t>w(n),freq(m),sums(1<<m);vector<uint32_t>den(nf),prefix(nf+1),fs(nf),values(ns+1),result(nc+1);
 for(size_t row=0;row<nr;++row){int64_t total=0;for(auto&x:w){points>>x;total+=x;}if(!points||total)throw runtime_error("point");fill(result.begin(),result.end(),0);
  for(size_t apex=0;apex<n;++apex){int64_t a=w[apex];size_t j=0;for(size_t i=0;i<n;++i)if(i!=apex)freq[j++]=w[i];sums[0]=0;
   for(size_t mask=1;mask<sums.size();++mask){size_t bit=mask&-mask;sums[mask]=sums[mask^bit]+freq[__builtin_ctzll(bit)];}
   prefix[0]=1;for(size_t k=0;k<nf;++k){auto q=sums[masks[k]];den[k]=mul(mod(q+a*heads[k]),mod(q+a*(heads[k]+int64_t(weights[k]))));if(!den[k])throw runtime_error("pole");prefix[k+1]=mul(prefix[k],den[k]);}
   auto back=power(prefix[nf],P-2);for(size_t k=nf;k-->0;){fs[k]=mul(mul(back,prefix[k]),weights[k]);back=mul(back,den[k]);}
   values[0]=1;for(size_t state=1;state<=ns;++state){uint64_t sum=0;for(size_t term=starts[state-1];term<starts[state];++term){sum+=mul(values[left[term]],fs[factor[term]]);if(sum>=P)sum-=P;}values[state]=sum;}
   auto prefactor=power(mod(-a),n-4);for(size_t col=0;col<nc;++col){uint64_t sum=result[col]+uint64_t(mul(prefactor,values[roots[col]]));result[col]=sum>=P?sum-P:sum;}
  }
  uint32_t target=1;for(auto x:w)target=mul(target,mod(x));result[nc]=power(target,P-2);if(n%2==0)result[nc]=(P-result[nc])%P;
  out.write((char*)result.data(),result.size()*4);if((row+1)%100==0)cerr<<"ROWS "<<row+1<<"\n";
 }
 return 0;
}catch(const exception&e){cerr<<e.what()<<"\n";return 2;}}
