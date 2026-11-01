// Full symmetric orbit sums at (-x-(N-2),1,...,1,x).
// A formal epsilon perturbation resolves removable pair-difference poles.
// Evaluate epsilon^(N-2)*R through degree N-2 and check every pole cancels.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

static constexpr uint64_t P=1000003;
static constexpr int CAP=20;
using Poly=std::array<uint64_t,CAP>;
static int degree;
static uint64_t mod(int64_t x) { x%=int64_t(P); return x<0?x+P:x; }
static uint64_t power(uint64_t a,uint64_t n) {
    uint64_t out=1;
    while(n) { if(n&1)out=out*a%P; a=a*a%P; n>>=1; }
    return out;
}
static Poly mul(const Poly&a,const Poly&b) {
    Poly out{};
    for(int i=0;i<=degree;++i)if(a[i])
        for(int j=0;j+i<=degree;++j)if(b[j])out[i+j]+=a[i]*b[j];
    for(int i=0;i<=degree;++i)out[i]%=P;
    return out;
}
static Poly edge(int64_t q0,int64_t q1,int64_t a0,int64_t a1,int sign) {
    uint64_t d0=mod(q0)*mod(q0+sign*a0)%P;
    uint64_t d1=(mod(q0)*mod(q1+sign*a1)+mod(q1)*mod(q0+sign*a0))%P;
    uint64_t d2=mod(q1)*mod(q1+sign*a1)%P;
    Poly out{};
    if(d0) {
        uint64_t inv=power(d0,P-2);
        Poly z{};z[0]=inv;
        for(int j=1;j<degree;++j) {
            uint64_t s=d1*z[j-1]%P;
            if(j>=2)s=(s+d2*z[j-2])%P;
            z[j]=(P-s)*inv%P;
        }
        for(int j=1;j<=degree;++j)out[j]=z[j-1];
    } else {
        if(!d1)throw std::runtime_error("higher-order pole or singular path");
        out[0]=power(d1,P-2);
        uint64_t ratio=(P-d2)*out[0]%P;
        for(int j=1;j<=degree;++j)out[j]=out[j-1]*ratio%P;
    }
    return out;
}
static std::vector<uint32_t> read(std::ifstream&f,size_t n) {
    std::vector<uint32_t>a(n);
    f.read(reinterpret_cast<char*>(a.data()),n*sizeof(uint32_t));
    if(!f)throw std::runtime_error("truncated DAG");
    return a;
}
int main(int argc,char**argv) {
 try {
    if(argc!=5&&argc!=6)throw std::runtime_error("DAG X_START ROWS OUTPUT_U32 [OUTLIERS]");
    auto started=std::chrono::steady_clock::now();
    std::ifstream input(argv[1],std::ios::binary);
    uint64_t h[6];input.read(reinterpret_cast<char*>(h),sizeof(h));
    if(!input||h[0]!=0x445053594D545245ULL)throw std::runtime_error("bad DAG");
    uint64_t N=h[1],states=h[2],terms=h[3],columns=h[4],used_count=h[5];
    if(N<5||N>=CAP)throw std::runtime_error("unsupported arity");
    degree=N-2;
    auto starts=read(input,states+1),left=read(input,terms),right=read(input,terms);
    auto bridge=read(input,terms),roots=read(input,columns),used=read(input,used_count);
    if(starts.back()!=terms)throw std::runtime_error("bad offsets");
    for(uint64_t s=1;s<=states;++s)for(uint64_t j=starts[s-1];j<starts[s];++j)
        if(left[j]>=s||right[j]>=s)throw std::runtime_error("non-topological DAG");
    int64_t x_start=std::stoll(argv[2]),count=std::stoll(argv[3]);
    int outliers=argc==6?std::stoi(argv[5]):1;
    if(outliers!=1&&outliers!=2)throw std::runtime_error("one or two outliers supported");
    if(x_start<=int64_t(N))throw std::runtime_error("x must exceed arity");
    std::ofstream output(argv[4],std::ios::binary);
    uint64_t masks=1ULL<<(N-1);
    std::vector<Poly>values(states+1),factors(2*masks),totals(columns);
    values[0][0]=1;factors[0][0]=1;
    std::vector<int64_t>base(N),slope(N),f0(N-1),f1(N-1),q0(masks),q1(masks);
    std::vector<uint32_t>row(columns+1);
    for(int64_t r=0;r<count;++r) {
        int64_t x=x_start+(outliers==1?r:r%31);
        std::fill(base.begin(),base.end(),1);
        base[0]=-x-int64_t(N-2);base[N-1]=x;
        if(outliers==2) {
            int64_t y=x_start+100+r/31;
            base[N-2]=y;base[0]-=y-1;
        }
        std::fill(slope.begin(),slope.end(),0);
        for(uint64_t i=1;i<N-outliers;++i){slope[i]=i;slope[0]-=i;}
        std::fill(totals.begin(),totals.end(),Poly{});
        for(uint64_t apex=0;apex<N;++apex) {
            uint64_t pos=0;
            for(uint64_t j=0;j<N;++j)if(j!=apex){f0[pos]=base[j];f1[pos++]=slope[j];}
            q0[0]=q1[0]=0;
            for(uint64_t mask=1;mask<masks;++mask) {
                uint64_t bit=mask&-mask,index=__builtin_ctzll(bit);
                q0[mask]=q0[mask^bit]+f0[index];q1[mask]=q1[mask^bit]+f1[index];
            }
            for(auto index:used)factors[index]=edge(q0[index/2],q1[index/2],base[apex],slope[apex],index&1?-1:1);
            for(uint64_t state=1;state<=states;++state) {
                Poly sum{};
                for(uint64_t j=starts[state-1];j<starts[state];++j) {
                    Poly value=right[j]?mul(values[left[j]],values[right[j]]):values[left[j]];
                    if(bridge[j])value=mul(value,factors[bridge[j]]);
                    for(int k=0;k<=degree;++k)sum[k]+=value[k];
                }
                for(int k=0;k<=degree;++k)sum[k]%=P;
                values[state]=sum;
            }
            Poly pre{};pre[0]=1;
            Poly minus_a{};minus_a[0]=mod(-base[apex]);minus_a[1]=mod(-slope[apex]);
            for(uint64_t j=0;j<N-4;++j)pre=mul(pre,minus_a);
            for(uint64_t j=0;j<columns;++j) {
                Poly value=mul(pre,values[roots[j]]);
                for(int k=0;k<=degree;++k)totals[j][k]=(totals[j][k]+value[k])%P;
            }
        }
        for(uint64_t j=0;j<columns;++j) {
            for(int k=0;k<degree;++k)if(totals[j][k])throw std::runtime_error("uncancelled difference pole");
            row[j]=totals[j][degree];
        }
        uint64_t target_den=1;
        for(auto b:base)target_den=target_den*mod(b)%P;
        uint64_t target=power(target_den,P-2);
        if((N-1)&1)target=(P-target)%P;
        row[columns]=target;
        output.write(reinterpret_cast<char*>(row.data()),row.size()*sizeof(uint32_t));
        if(!output)throw std::runtime_error("output write failed");
        if((r+1)%10==0||r+1==count)std::cerr<<"ROWS "<<r+1<<" SECONDS "
            <<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<"\n";
    }
    std::cerr<<"DONE "<<count<<" ROWS "<<columns<<" COLUMNS; ALL REMOVABLE POLES CANCELLED\n";
 } catch(const std::exception&e) {std::cerr<<e.what()<<"\n";return 1;}
}
