// Exact rational evaluator for the signed-subtree subset DAG.
// Edges are reduced GMP fractions 1/[q(q+sign*a)], in contrast to the
// common-denominator integer engine. D is computed for diagnostics only.
// Compile: g++ -O3 -std=c++17 overnight_lower_rational_dp.cpp -lgmpxx -lgmp -o /tmp/overnight_lower_rational_dp
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <gmpxx.h>
#include <iostream>
#include <stdexcept>
#include <vector>

static std::vector<uint32_t> read(std::ifstream& f, size_t n) {
    std::vector<uint32_t> out(n);
    f.read(reinterpret_cast<char*>(out.data()), n*sizeof(uint32_t));
    if (!f) throw std::runtime_error("truncated DAG");
    return out;
}
static uint64_t absolute(int64_t a) { return a < 0 ? uint64_t(-a) : uint64_t(a); }

int main(int argc, char** argv) {
 try {
    if (argc != 4) throw std::runtime_error("DAG POINTS_TEXT OUTPUT_JSONL");
    auto start = std::chrono::steady_clock::now();
    std::ifstream input(argv[1], std::ios::binary);
    uint64_t h[6]; input.read(reinterpret_cast<char*>(h), sizeof(h));
    if (!input || h[0] != 0x445053594D545245ULL) throw std::runtime_error("bad DAG");
    auto N=h[1], states=h[2], terms=h[3], columns=h[4], used_count=h[5];
    if (N < 5 || N > 16) throw std::runtime_error("unsupported arity");
    auto starts=read(input,states+1), left=read(input,terms), right=read(input,terms);
    auto bridge=read(input,terms), roots=read(input,columns), used=read(input,used_count);
    if (starts.back()!=terms) throw std::runtime_error("bad term offsets");
    std::vector<unsigned> degree(states+1);
    for (uint64_t s=1;s<=states;++s) {
        if (starts[s]==starts[s-1]) throw std::runtime_error("empty state");
        for (uint64_t j=starts[s-1];j<starts[s];++j) {
            if (left[j]>=s || right[j]>=s) throw std::runtime_error("non-topological DAG");
            auto d=degree[left[j]]+degree[right[j]]+unsigned(bridge[j]!=0);
            if (j==starts[s-1]) degree[s]=d;
            else if (degree[s]!=d) throw std::runtime_error("inhomogeneous edge degree");
        }
    }
    for (auto root:roots) if (degree[root]!=N-2) throw std::runtime_error("wrong root degree");
    uint64_t masks=1ULL<<(N-1);
    std::vector<int64_t> point(N), frequencies(N-1), sums(masks);
    std::vector<std::vector<int64_t>> linear_q(N, std::vector<int64_t>(used_count));
    std::vector<mpq_class> factors(2*masks), values(states+1), totals(columns+1);
    factors[0]=1; values[0]=1;
    std::ifstream points(argv[2]); uint64_t rows, arity;
    points>>rows>>arity;
    if (!points || arity!=N) throw std::runtime_error("bad point header");
    std::ofstream out(argv[3]);
    for (uint64_t r=0;r<rows;++r) {
        int64_t sum=0;
        for(auto& x:point) { points>>x; sum+=x; }
        if (!points || sum) throw std::runtime_error("invalid sum-zero point");
        mpz_class D=1, target_den=1;
        for (auto x:point) {
            if(!x) throw std::runtime_error("zero target denominator");
            mpz_lcm_ui(D.get_mpz_t(), D.get_mpz_t(), absolute(x));
            target_den*=x;
        }
        for (uint64_t apex=0;apex<N;++apex) {
            uint64_t k=0;
            for (uint64_t j=0;j<N;++j) if(j!=apex) frequencies[k++]=point[j];
            sums[0]=0;
            for (uint64_t mask=1;mask<masks;++mask) {
                uint64_t bit=mask&-mask;
                sums[mask]=sums[mask^bit]+frequencies[__builtin_ctzll(bit)];
            }
            for(uint64_t j=0;j<used_count;++j) {
                auto index=used[j];
                auto q=sums[index/2], shifted=q+(index&1?-point[apex]:point[apex]);
                if(!q || !shifted) throw std::runtime_error("singular point");
                linear_q[apex][j]=q;
                mpz_lcm_ui(D.get_mpz_t(),D.get_mpz_t(),absolute(q));
                mpz_lcm_ui(D.get_mpz_t(),D.get_mpz_t(),absolute(shifted));
            }
        }
        mpz_class common, multiplier;
        mpq_class tmp;
        std::fill(totals.begin(),totals.end(),0);
        for(uint64_t apex=0;apex<N;++apex) {
            for(uint64_t j=0;j<used_count;++j) {
                auto index=used[j];
                auto q=linear_q[apex][j], den=q*(q+(index&1?-point[apex]:point[apex]));
                factors[index]=mpq_class(1,den);
                factors[index].canonicalize();
            }
            for(uint64_t s=1;s<=states;++s) {
                values[s]=0;
                for(uint64_t j=starts[s-1];j<starts[s];++j) {
                    tmp=values[left[j]]*values[right[j]];
                    if(bridge[j]) tmp*=factors[bridge[j]];
                    values[s]+=tmp;
                }
            }
            multiplier=-point[apex];
            mpz_pow_ui(multiplier.get_mpz_t(),multiplier.get_mpz_t(),N-4);
            for(uint64_t j=0;j<columns;++j) totals[j]+=multiplier*values[roots[j]];
        }
        totals[columns]=mpq_class(1,target_den);
        if((N-1)&1) totals[columns]=-totals[columns];
        totals[columns].canonicalize();
        common=1;
        for(auto& v:totals) mpz_lcm(common.get_mpz_t(),common.get_mpz_t(),v.get_den_mpz_t());
        out<<"{\"index\":"<<r<<",\"point\":[";
        for(uint64_t j=0;j<N;++j) out<<(j?",":"")<<point[j];
        out<<"],\"scale\":\""<<common<<"\",\"values\":[";
        size_t digits=0;
        for(uint64_t j=0;j<=columns;++j) {
            mpz_class integer=totals[j].get_num()*(common/totals[j].get_den());
            out<<(j?",":"")<<"\""<<integer<<"\"";
            digits=std::max(digits,mpz_sizeinbase(integer.get_mpz_t(),10));
        }
        out<<"]}\n"; out.flush();
        if(!out) throw std::runtime_error("output write failed");
        std::cout<<"EXACT ROW "<<r+1<<" OF "<<rows<<" MAX_DIGITS "<<digits
                 <<" D_DIGITS "<<mpz_sizeinbase(D.get_mpz_t(),10)<<" SECONDS "
                 <<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
    }
 } catch(const std::exception& e) { std::cerr<<e.what()<<"\n"; return 1; }
}
