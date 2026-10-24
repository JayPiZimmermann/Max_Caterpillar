// Independent closed-form check (own derivation): n vertices, weights c, Gamma.
// locality (T,order of O) seen iff: for each o in O, upweight(o)=Gamma_o (T above all O);
// sum_T Gamma = c(E(T)); sum_T [s(G_t)-s(d_t-G_t)] != 0.
#include <bits/stdc++.h>
using namespace std;
int n; int c[8][8]; int G[8];
long W(){
  long tot=0; vector<int> V(n); iota(V.begin(),V.end(),0);
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int d=b+1;d<n;d++){
    int T[3]={a,b,d}; int cE=c[a][b]+c[a][d]+c[b][d];
    if(G[a]+G[b]+G[d]!=cE) continue;
    long L=0; for(int t:T){int dt=0; for(int t2:T) if(t2!=t) dt+=c[t][t2]; L+=max(G[t],0)-max(dt-G[t],0);}
    if(L==0) continue;
    vector<int> O; for(int v=0;v<n;v++) if(v!=a&&v!=b&&v!=d) O.push_back(v);
    sort(O.begin(),O.end());
    do{ bool ok=true;
      for(size_t i=0;i<O.size()&&ok;i++){int up=c[O[i]][a]+c[O[i]][b]+c[O[i]][d]; for(size_t j=0;j<i;j++) up+=c[O[i]][O[j]]; if(up!=G[O[i]]) ok=false;}
      if(ok) tot++; }while(next_permutation(O.begin(),O.end()));
  }
  return tot;
}
int main(int argc,char**argv){
  n=atoi(argv[1]); int mode=atoi(argv[2]);
  long fact=1; for(int i=2;i<=n-3;i++) fact*=i;
  vector<pair<int,int>> E; for(int i=0;i<n;i++)for(int j=i+1;j<n;j++) E.push_back({i,j});
  long best=0;
  if(mode==0){ // exhaustive c in {0,1}, Gamma in [-R,R]
    int R=atoi(argv[3]);
    for(long m=0;m<(1L<<E.size());m++){
      for(size_t k=0;k<E.size();k++){c[E[k].first][E[k].second]=c[E[k].second][E[k].first]=(m>>k)&1;}
      int base=2*R+1; long tot=1; for(int i=0;i<n;i++) tot*=base;
      for(long g=0;g<tot;g++){ long h=g; for(int i=0;i<n;i++){G[i]=h%base-R; h/=base;}
        long w=W(); if(w>best){best=w; printf("best f=%g m=%ld G=",(double)w/fact,m); for(int i=0;i<n;i++)printf("%d ",G[i]); printf("\n"); fflush(stdout);} }
    }
  } else { // random: weights 0..Wmax, Gamma chosen as up-weights of random orders / random
    int Wm=atoi(argv[3]); long S=atol(argv[4]); mt19937 rng(atoi(argv[5]));
    for(long s=0;s<S;s++){
      for(auto e:E){int w=rng()%(Wm+1); c[e.first][e.second]=c[e.second][e.first]=w;}
      for(int i=0;i<n;i++){ int r=rng()%3; int deg=0; for(int j=0;j<n;j++) deg+=c[i][j];
        if(r==0) G[i]=deg; else if(r==1){int up=0; for(int j=0;j<n;j++) if(j!=i && rng()%2) up+=c[i][j]; G[i]=up;} else G[i]=(int)(rng()%13)-9; }
      long w=W(); if(w>best){best=w; printf("best f=%g\n",(double)w/fact); fflush(stdout);} }
  }
  printf("FINAL best f=%g\n",(double)best/fact);
}
