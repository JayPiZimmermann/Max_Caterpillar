// Exhaustive scan: per-neuron locality counts for second-layer neurons
//   U = relu(g),  g(x) = sum_i gam_i x_i + sum_{e} c_e max(x_i,x_j)
// on a braid first layer, at localities (T, order of O) in the positive orthant.
// A neuron "sees" locality (T,rho) iff g vanishes on the open cell
// (conditions (a),(c)) and the m-th mixed difference
//   Lam = sum_{S subset T} (-1)^{m-|S|} relu( v(S) + c(E_T(S)) ) != 0,
// v_t = gam_t + sum_{o in O} c_{to}.
// Mode "convex": c_e in {0,1} (unit weights, all graphs up to iso).
// Mode "signed": c_e in {-1,0,1}.
// For each graph and m, maximize over integer gam in [-R,R] the number W of
// seen localities; report max_W/(N-m)!  (= sum_T Pr_rho[seen]).
#include <bits/stdc++.h>
using namespace std;
int N, R; bool SIGNED=false;
int c[8][8];
long long fact(int n){long long f=1;for(int i=2;i<=n;i++)f*=i;return f;}
int main(int argc,char**argv){
  N=atoi(argv[1]); R=atoi(argv[2]); if(argc>3 && string(argv[3])=="signed") SIGNED=true;
  int E=N*(N-1)/2; vector<pair<int,int>> ed; for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)ed.push_back({i,j});
  // enumerate graphs (weight vectors) up to isomorphism
  int base = SIGNED?3:2; long long total=1; for(int k=0;k<E;k++) total*=base;
  vector<int> perm(N); iota(perm.begin(),perm.end(),0); vector<vector<int>> perms;
  do perms.push_back(perm); while(next_permutation(perm.begin(),perm.end()));
  vector<int> eidx(N*N); for(int k=0;k<E;k++){eidx[ed[k].first*N+ed[k].second]=k;eidx[ed[k].second*N+ed[k].first]=k;}
  set<long long> seen; vector<vector<int>> reps;
  for(long long code=0;code<total;code++){
    vector<int> w(E); long long t=code; for(int k=0;k<E;k++){w[k]=t%base; t/=base;}
    // canonical: min code over perms
    long long best=LLONG_MAX;
    for(auto&p:perms){ long long cc=0; for(int k=E-1;k>=0;k--){ int a=p[ed[k].first],b=p[ed[k].second]; cc=cc*base+w[eidx[a*N+b]];} best=min(best,cc);}
    if(seen.insert(best).second) reps.push_back(w);
  }
  fprintf(stderr,"graphs up to iso: %zu\n",reps.size());
  int V=2*R+1;
  vector<double> bestRatio(N+1,0); vector<string> bestDesc(N+1);
  for(auto&w:reps){
    for(int i=0;i<N;i++)for(int j=0;j<N;j++)c[i][j]=0;
    for(int k=0;k<E;k++){int v=SIGNED?(w[k]==2?-1:w[k]):w[k]; c[ed[k].first][ed[k].second]=c[ed[k].second][ed[k].first]=v;}
    for(int m=3;m<=N;m++){
      unordered_map<long long,long long> cnt;
      for(int Tm=0;Tm<(1<<N);Tm++){ if(__builtin_popcount(Tm)!=m) continue;
        vector<int> T,O; for(int i=0;i<N;i++) (Tm>>i&1?T:O).push_back(i);
        // v base (without gamma): sum_{o in O} c_to
        vector<int> vb(m); for(int a=0;a<m;a++){int s=0; for(int o:O) s+=c[T[a]][o]; vb[a]=s;}
        int cET=0; for(int a=0;a<m;a++)for(int b=a+1;b<m;b++) cET+=c[T[a]][T[b]];
        // sum condition: sum_T v_t + c(E(T)) = 0 -> sum_T gam_t = -(sum vb + cET)
        int target=-(accumulate(vb.begin(),vb.end(),0)+cET);
        // enumerate gamma_T
        vector<vector<int>> gTs; vector<int> g(m);
        long long nT=1; for(int a=0;a<m-1;a++) nT*=V;
        for(long long q=0;q<nT;q++){ long long t=q; int s=0; for(int a=0;a<m-1;a++){g[a]=(int)(t%V)-R; t/=V; s+=g[a];}
          g[m-1]=target-s; if(g[m-1]<-R||g[m-1]>R) continue;
          // Lambda
          long long Lam=0;
          for(int S=0;S<(1<<m);S++){ long long val=0; for(int a=0;a<m;a++) if(S>>a&1) val+=g[a]+vb[a];
            for(int a=0;a<m;a++)for(int b=a+1;b<m;b++) if((S>>a&1)||(S>>b&1)) val+=c[T[a]][T[b]];
            long long r=max(val,0LL); if((m-__builtin_popcount(S))%2) Lam-=r; else Lam+=r; }
          if(Lam!=0) gTs.push_back(g);
        }
        if(gTs.empty()) continue;
        // orders of O
        vector<int> ord=O; sort(ord.begin(),ord.end());
        do{ // ord[0] highest
          vector<int> gam(N,0); bool ok=true;
          for(int a=0;a<(int)ord.size();a++){ int o=ord[a]; int D=0; for(int b=a+1;b<(int)ord.size();b++) D+=c[o][ord[b]]; gam[o]=-D; if(gam[o]<-R||gam[o]>R) ok=false; }
          if(!ok) continue;
          for(auto&gt:gTs){ for(int a=0;a<m;a++) gam[T[a]]=gt[a]; long long key=0; for(int i=0;i<N;i++) key=key*V+(gam[i]+R); cnt[key]++; }
        }while(next_permutation(ord.begin(),ord.end()));
      }
      long long mx=0,arg=0; for(auto&kv:cnt) if(kv.second>mx){mx=kv.second;arg=kv.first;}
      double ratio=(double)mx/fact(N-m);
      if(ratio>bestRatio[m]+1e-12){ bestRatio[m]=ratio; ostringstream os; os<<"W="<<mx<<" edges:"; for(int k=0;k<E;k++) if(c[ed[k].first][ed[k].second]) os<<" "<<ed[k].first<<ed[k].second<<"("<<c[ed[k].first][ed[k].second]<<")"; os<<" gam:"; vector<int> gg(N); long long t=arg; for(int i=N-1;i>=0;i--){gg[i]=(int)(t%V)-R;t/=V;} for(int i=0;i<N;i++) os<<" "<<gg[i]; bestDesc[m]=os.str(); }
    }
  }
  for(int m=3;m<=N;m++) printf("N=%d m=%d max W/(N-m)! = %.6f  (all localities: C(N,m)=%lld)  pow=%.4f  %s\n",N,m,bestRatio[m],fact(N)/fact(m)/fact(N-m),pow(bestRatio[m],1.0/m),bestDesc[m].c_str());
}
