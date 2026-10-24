// m=3 scan for convex braid neurons with general small integer weights.
// Uses the closed forms (derived in NOTES.md, section "m=3 formulas"):
//   Gam_x = gam_x + deg_c(x);  locality (T,rho) seen iff
//   (a) every o in O has up-weight (neighbours above, T counts as above) = Gam_o,
//   (c) sum_{t in T} Gam_t = c(E(T)),
//   (L) Lam = sum_{t in T} clamp(Gam_t, 0, d_t) - c(E(T)) != 0,  d_t = c(t, T\t).
// The program ALSO recomputes Lam by brute force over the 8 cube corners
// (germ G(z) = sum v_t z_t + sum_{e in T} c_e max(z_e)) and aborts on mismatch.
// Modes: argv[1]=N, argv[2]=maxweight W (weights 0..W), argv[3]=samples
//   (0 = all weight vectors, no iso reduction), argv[4]=seed, argv[5]=R (|Gam| range slack)
#include <bits/stdc++.h>
using namespace std;
int N; int c[9][9];
long long fact(int n){long long f=1;for(int i=2;i<=n;i++)f*=i;return f;}
int main(int argc,char**argv){
  N=atoi(argv[1]); int W=atoi(argv[2]); long long samples=atoll(argv[3]); unsigned seed=atoi(argv[4]); int R=atoi(argv[5]);
  mt19937 rng(seed);
  int E=N*(N-1)/2; vector<pair<int,int>> ed; for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)ed.push_back({i,j});
  long long total=1; for(int k=0;k<E;k++) total*=(W+1);
  long long iters = samples? samples: total;
  double best=0; string bestd; map<int,long long> hist;
  for(long long it=0; it<iters; it++){
    vector<int> w(E);
    if(samples){ double dens = uniform_real_distribution<double>(0.05,0.9)(rng);
      for(int k=0;k<E;k++){ w[k]= (uniform_real_distribution<double>(0,1)(rng)<dens)? 1+rng()%W : 0; } }
    else { long long t=it; for(int k=0;k<E;k++){w[k]=t%(W+1); t/=(W+1);} }
    for(int i=0;i<N;i++)for(int j=0;j<N;j++)c[i][j]=0;
    for(int k=0;k<E;k++) c[ed[k].first][ed[k].second]=c[ed[k].second][ed[k].first]=w[k];
    vector<int> deg(N,0); for(int i=0;i<N;i++)for(int j=0;j<N;j++)deg[i]+=c[i][j];
    // key: Gamma vector, value: count of seen (T,rho)
    unordered_map<string,long long> cnt;
    int m=3;
    for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)for(int d=b+1;d<N;d++){
      int T[3]={a,b,d}; vector<int> O; for(int i=0;i<N;i++) if(i!=a&&i!=b&&i!=d) O.push_back(i);
      int cET=c[a][b]+c[a][d]+c[b][d]; if(cET==0) continue;
      int dd[3]; for(int q=0;q<3;q++){dd[q]=0; for(int r=0;r<3;r++) dd[q]+=c[T[q]][T[r]];}
      // enumerate Gamma_T in range [-R, maxdeg+R] with sum = cET and Lam != 0
      vector<array<int,3>> GTs; int lo=-R, hi=*max_element(deg.begin(),deg.end())+R;
      for(int g0=lo;g0<=hi;g0++)for(int g1=lo;g1<=hi;g1++){ int g2=cET-g0-g1; if(g2<lo||g2>hi) continue;
        int G[3]={g0,g1,g2}; long long lam=-cET; for(int q=0;q<3;q++) lam+=min(max(G[q],0),dd[q]);
        // brute-force check: v_t = Gam_t - d_t ; corners
        long long lam2=0; for(int S=0;S<8;S++){ long long val=0; for(int q=0;q<3;q++) if(S>>q&1) val+=G[q]-dd[q];
            for(int q=0;q<3;q++)for(int r=q+1;r<3;r++) if((S>>q&1)||(S>>r&1)) val+=c[T[q]][T[r]];
            long long rr=max(val,0LL); if((3-__builtin_popcount(S))%2) lam2-=rr; else lam2+=rr; }
        if(lam!=lam2){ fprintf(stderr,"MISMATCH\n"); return 1; }
        if(lam!=0) GTs.push_back({g0,g1,g2}); }
      if(GTs.empty()) continue;
      vector<int> ord=O;
      do{ vector<int> Gam(N,INT_MIN); bool ok=true;
        for(size_t p=0;p<ord.size();p++){ int o=ord[p]; int up=c[o][a]+c[o][b]+c[o][d]; for(size_t q=0;q<p;q++) up+=c[o][ord[q]]; Gam[o]=up; }
        for(auto&g:GTs){ Gam[a]=g[0];Gam[b]=g[1];Gam[d]=g[2]; string key((char*)Gam.data(), N*sizeof(int)); cnt[key]++; }
      }while(next_permutation(ord.begin(),ord.end()));
    }
    long long mx=0; string arg; for(auto&kv:cnt) if(kv.second>mx){mx=kv.second;arg=kv.first;}
    double ratio=(double)mx/fact(N-3); hist[(int)floor(ratio+1e-9)]++;
    if(ratio>best+1e-12){ best=ratio; ostringstream os; os<<"ratio="<<ratio<<" edges:"; for(int k=0;k<E;k++) if(w[k]) os<<" "<<ed[k].first<<ed[k].second<<"("<<w[k]<<")"; os<<" Gam:"; const int*g=(const int*)arg.data(); for(int i=0;i<N;i++) os<<" "<<g[i]; bestd=os.str(); fprintf(stderr,"%s\n",bestd.c_str()); }
  }
  printf("N=%d W=%d samples=%lld seed=%u R=%d : max sum_T Pr = %.6f (N-2=%d)\n  %s\n",N,W,samples,seed,R,best,N-2,bestd.c_str());
  for(auto&kv:hist) printf("  floor(ratio)=%d : %lld graphs\n",kv.first,kv.second);
}
