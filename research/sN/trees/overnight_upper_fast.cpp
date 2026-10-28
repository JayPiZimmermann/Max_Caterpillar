#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
constexpr uint64_t P=1000000007ULL;
uint32_t mul(uint64_t a,uint64_t b){return a*b%P;}
uint32_t power(uint32_t a,uint64_t k){uint32_t r=1;for(;k;k>>=1,a=mul(a,a))if(k&1)r=mul(r,a);return r;}
template<class T> vector<T> read_vec(ifstream& f,size_t n){vector<T>x(n);f.read((char*)x.data(),n*sizeof(T));if(!f)throw runtime_error("short binary input");return x;}
int main(int argc,char**argv){try{
 if(argc<4)throw runtime_error("usage: ENGINE.bin POINTS.txt OUTPUT.u32 [START] [COUNT]");
 auto started=chrono::steady_clock::now();ifstream f(argv[1],ios::binary);auto h=read_vec<uint64_t>(f,6);
 if(h[0]!=0x5550504552504149ULL)throw runtime_error("bad engine magic");
 size_t n=h[1],nf=h[2],np=h[3],nu=h[4],nc=h[5],ne=n-2;
 auto forms=read_vec<int32_t>(f,nf*n);auto pairs=read_vec<uint32_t>(f,np*2);
 auto incidence=read_vec<uint32_t>(f,nu*ne);auto apices=read_vec<uint8_t>(f,nu);
 auto offsets=read_vec<uint64_t>(f,nc+1);if(offsets.back()!=nu)throw runtime_error("bad offsets");
 ifstream points(argv[2]);size_t rows,arity;points>>rows>>arity;if(arity!=n)throw runtime_error("bad arity");
 size_t start=argc>4?stoull(argv[4]):0,count=argc>5?stoull(argv[5]):rows-start,end=min(rows,start+count);
 fstream out(argv[3],ios::binary|ios::in|ios::out);if(!out){ofstream create(argv[3],ios::binary);create.close();out.open(argv[3],ios::binary|ios::in|ios::out);}
 out.seekp(start*(nc+1)*4);vector<int64_t>w(n);vector<uint32_t>values(nf),prefix(nf+1),inv(nf),pf(np),ap(n),result(nc+1);
 for(size_t row=0;row<end;++row){int64_t total=0;for(auto&x:w){points>>x;total+=x;}if(!points||total)throw runtime_error("bad frequency row");if(row<start)continue;
  prefix[0]=1;for(size_t j=0;j<nf;++j){int64_t q=0;for(size_t i=0;i<n;++i)q+=forms[j*n+i]*w[i];q%=int64_t(P);if(q<0)q+=P;if(!q)throw runtime_error("linear factor pole");values[j]=q;prefix[j+1]=mul(prefix[j],q);}
  uint32_t back=power(prefix[nf],P-2);for(size_t j=nf;j-->0;){inv[j]=mul(back,prefix[j]);back=mul(back,values[j]);}
  for(size_t j=0;j<np;++j)pf[j]=mul(inv[pairs[2*j]],inv[pairs[2*j+1]]);
  uint32_t target=1;for(size_t i=0;i<n;++i){int64_t q=w[i]%int64_t(P);if(q<0)q+=P;if(!q)throw runtime_error("coordinate pole");target=mul(target,q);ap[i]=power((P-q)%P,n-4);}
  for(size_t col=0;col<nc;++col){uint64_t sum=0;for(size_t u=offsets[col];u<offsets[col+1];++u){uint32_t v=ap[apices[u]];for(size_t j=0;j<ne;++j)v=mul(v,pf[incidence[u*ne+j]]);sum+=v;if(sum>=P)sum-=P;}result[col]=sum;}
  result[nc]=power(target,P-2);if(n%2==0)result[nc]=(P-result[nc])%P;
  out.write((char*)result.data(),result.size()*4);if(!out)throw runtime_error("output write failed");
  if((row+1)%320==0||row+1==end){out.flush();cerr<<"ROWS "<<row+1<<" SECONDS "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";}
 }
 out.flush();return 0;
 }catch(const exception&e){cerr<<"ERROR "<<e.what()<<"\n";return 2;}}
