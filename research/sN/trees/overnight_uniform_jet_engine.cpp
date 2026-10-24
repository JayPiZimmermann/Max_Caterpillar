// Full orbit sums: principal part plus a bounded positive Laurent jet.
// Every edge is scaled by epsilon^2, allowing a zero apex and double poles.
// Derived from the reviewed shared-DP evaluator; modular diagnostics only.
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

static constexpr uint64_t P=1000003;
static constexpr int CAP=32;
using Poly=std::array<uint64_t,CAP>;
static int degree;
static uint64_t mod(int64_t x){x%=int64_t(P);return x<0?x+P:x;}
static uint64_t power(uint64_t a,uint64_t n){uint64_t z=1;while(n){if(n&1)z=z*a%P;a=a*a%P;n>>=1;}return z;}
static Poly mul(const Poly&a,const Poly&b){Poly z{};for(int i=0;i<=degree;++i)if(a[i])for(int j=0;i+j<=degree;++j)if(b[j])z[i+j]+=a[i]*b[j];for(int i=0;i<=degree;++i)z[i]%=P;return z;}
static Poly edge(int64_t q0,int64_t q1,int64_t a0,int64_t a1,int sign){
    uint64_t d0=mod(q0)*mod(q0+sign*a0)%P;
    uint64_t d1=(mod(q0)*mod(q1+sign*a1)+mod(q1)*mod(q0+sign*a0))%P;
    uint64_t d2=mod(q1)*mod(q1+sign*a1)%P;Poly z{};
    if(d0){
        uint64_t inv=power(d0,P-2);Poly w{};w[0]=inv;
        for(int j=1;j<=degree-2;++j){uint64_t s=d1*w[j-1]%P;if(j>=2)s=(s+d2*w[j-2])%P;w[j]=(P-s)*inv%P;}
        for(int j=2;j<=degree;++j)z[j]=w[j-2];
    }else if(d1){
        z[1]=power(d1,P-2);uint64_t ratio=(P-d2)*z[1]%P;
        for(int j=2;j<=degree;++j)z[j]=z[j-1]*ratio%P;
    }else{
        if(!d2)throw std::runtime_error("path lies on a pole");
        z[0]=power(d2,P-2);
    }
    return z;
}
static std::vector<uint32_t> read(std::ifstream&f,size_t n){std::vector<uint32_t>a(n);f.read(reinterpret_cast<char*>(a.data()),n*sizeof(uint32_t));if(!f)throw std::runtime_error("truncated DAG");return a;}
int main(int argc,char**argv){try{
    if(argc!=5)throw std::runtime_error("DAG POINTS_TEXT OUTPUT_U32 MAX_EXPONENT");
    int max_exp=std::stoi(argv[4]);
    auto started=std::chrono::steady_clock::now();std::ifstream input(argv[1],std::ios::binary);uint64_t h[6];input.read(reinterpret_cast<char*>(h),sizeof(h));
    if(!input||h[0]!=0x445053594D545245ULL)throw std::runtime_error("bad DAG");
    uint64_t N=h[1],states=h[2],terms=h[3],columns=h[4],used_count=h[5];degree=2*N-4+max_exp;
    if(N<5||degree>=CAP)throw std::runtime_error("unsupported arity");
    auto starts=read(input,states+1),left=read(input,terms),right=read(input,terms),bridge=read(input,terms),roots=read(input,columns),used=read(input,used_count);
    if(starts.back()!=terms)throw std::runtime_error("bad DAG offsets");
    std::ifstream points(argv[2]);uint64_t count,arity;points>>count>>arity;if(arity!=N)throw std::runtime_error("wrong arity");
    std::ofstream output(argv[3],std::ios::binary);uint64_t masks=1ULL<<(N-1);
    std::vector<Poly>values(states+1),factors(2*masks),totals(columns);values[0][0]=1;factors[0][0]=1;
    std::vector<int64_t>base(N),slope(N),f0(N-1),f1(N-1),q0(masks),q1(masks);std::vector<uint32_t>row(columns+1);
    for(uint64_t r=0;r<count;++r){
        int64_t bs=0,ss=0;int zeros=0;uint64_t target_den=1;
        for(auto&x:base){points>>x;bs+=x;}
        for(auto&x:slope){points>>x;ss+=x;}
        if(!points||bs||ss)throw std::runtime_error("invalid zero-sum point");
        for(uint64_t i=0;i<N;++i){if(base[i])target_den=target_den*mod(base[i])%P;else{++zeros;target_den=target_den*mod(slope[i])%P;}}
        if(zeros!=1||!target_den)throw std::runtime_error("target pole must be simple");
        Poly target{};target[0]=1;
        for(uint64_t i=0;i<N;++i){
            Poly inv{};
            if(!base[i])inv[0]=power(mod(slope[i]),P-2);
            else{inv[0]=power(mod(base[i]),P-2);uint64_t rat=mod(-slope[i])*inv[0]%P;for(int k=1;k<=degree;++k)inv[k]=inv[k-1]*rat%P;}
            target=mul(target,inv);
        }
        std::fill(totals.begin(),totals.end(),Poly{});
        for(uint64_t apex=0;apex<N;++apex){
            uint64_t pos=0;for(uint64_t j=0;j<N;++j)if(j!=apex){f0[pos]=base[j];f1[pos++]=slope[j];}
            q0[0]=q1[0]=0;for(uint64_t mask=1;mask<masks;++mask){uint64_t bit=mask&-mask,index=__builtin_ctzll(bit);q0[mask]=q0[mask^bit]+f0[index];q1[mask]=q1[mask^bit]+f1[index];}
            for(auto index:used)factors[index]=edge(q0[index/2],q1[index/2],base[apex],slope[apex],index&1?-1:1);
            for(uint64_t state=1;state<=states;++state){
                Poly sum{};for(uint64_t j=starts[state-1];j<starts[state];++j){Poly v=right[j]?mul(values[left[j]],values[right[j]]):values[left[j]];if(bridge[j])v=mul(v,factors[bridge[j]]);for(int k=0;k<=degree;++k)sum[k]+=v[k];}
                for(int k=0;k<=degree;++k)sum[k]%=P;values[state]=sum;
            }
            Poly pre{};pre[0]=1;Poly minus_a{};minus_a[0]=mod(-base[apex]);minus_a[1]=mod(-slope[apex]);for(uint64_t j=0;j<N-4;++j)pre=mul(pre,minus_a);
            for(uint64_t j=0;j<columns;++j){Poly v=mul(pre,values[roots[j]]);for(int k=0;k<=degree;++k)totals[j][k]=(totals[j][k]+v[k])%P;}
        }
        for(int k=0;k<=degree;++k){
            for(uint64_t j=0;j<columns;++j)row[j]=totals[j][k];
            row[columns]=(k>=int(2*N-5))?target[k-(2*N-5)]:0;if((N-1)&1)row[columns]=(P-row[columns])%P;
            output.write(reinterpret_cast<char*>(row.data()),row.size()*sizeof(uint32_t));if(!output)throw std::runtime_error("write failed");
        }
        if((r+1)%10==0||r+1==count){output.flush();std::cerr<<"ROWS "<<r+1<<" SECONDS "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<"\n";}
    }
    std::cerr<<"DONE "<<count<<" ROWS "<<columns<<" COLUMNS\n";
}catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}}
