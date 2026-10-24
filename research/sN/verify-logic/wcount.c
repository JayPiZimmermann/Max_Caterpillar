/* Exact per-unit locality count for caterpillar face units (identity labelling).
   Usage: wcount N [mode]   mode: b (default) = Pass = (a) and (b'); a = (a) only.
   Enumerates every nonempty cut set S of {1..r}, r=N-2, every edge state
   (0 omit,1 lin,2 hinge; edge parent->child, hinge = relu(y_p - y_c)), every
   triple T (no apex pruning), and counts orders of the N-3 outside coordinates
   satisfying (a): for each o outside T, #hinge nbrs of o below o == mu_o, where
   mu_o = [apex]-[last]+[parent edge active]-#linear children (= deg_F - kappa).
   Also checks the structural claims of the cubic sketch:
   CaseI (|Neg|=1): every valid T = {0,u,w}, uw hinge; all valid edges in one
     F-component C*; tau_v := kappa_v - #hinge-leaf children == 1 on spine of C*.
   CaseII (|Neg|=2): at most one valid triple; it is {0,z,parent(z)}, z a
     linear leaf.  Reports max W = total/(N-3)! overall and per |Neg|. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N, r, nout;
static long long fact(int n){long long f=1;for(int i=2;i<=n;i++)f*=i;return f;}
int main(int argc,char**argv){
  N=atoi(argv[1]); int modeb = !(argc>2 && argv[2][0]=='a');
  r=N-2; nout=N-3;
  long long F=fact(nout);
  long long best=0, bestNeg[8]={0}; int bestS=0; long long bestSt=0;
  long long nunits=0, viol1=0, viol2=0, viol3=0, viol4=0, viol5=0;
  long long hist_valid_by_neg[8]={0};
  int par[16], lastv, spine[16];
  long long *dp = malloc(sizeof(long long)<<nout);
  int states[16];
  long long nst=1; for(int i=0;i<r;i++) nst*=3;
  for(int S=1; S < (1<<r); S++){            /* bit i-1 <-> position i in S */
    int maxS=0;
    memset(spine,0,sizeof spine); spine[1]=1;
    for(int j=1;j<=r;j++){
      int p=0; for(int i=1;i<j;i++) if(S>>(i-1)&1) p=i;
      par[j+1]=p+1;
      if(S>>(j-1)&1){ maxS=j; spine[j+1]=1; }
    }
    lastv=maxS+1;
    for(long long code=0; code<nst; code++){
      long long c=code; for(int i=0;i<r;i++){states[i]=c%3;c/=3;}
      nunits++;
      int mu[16]={0}, kap[16]; unsigned nb[16]={0}, linpar[16]={0};
      int hingeleafch[16]={0};
      mu[0]+=1; mu[lastv]-=1;
      for(int j=1;j<=r;j++){ int p=par[j+1], ch=j+1, s=states[j-1];
        if(s) mu[ch]+=1;
        if(s==1){ mu[p]-=1; linpar[ch]=1; }
        if(s==2){ nb[p]|=1u<<ch; nb[ch]|=1u<<p; if(!spine[ch]) hingeleafch[p]++; }
      }
      unsigned neg=0;
      for(int o=0;o<N;o++){ kap[o]=__builtin_popcount(nb[o])-mu[o]; if(kap[o]<0) neg|=1u<<o; }
      int nneg=__builtin_popcount(neg);
      /* components of F */
      int comp[16]; for(int o=0;o<N;o++) comp[o]=-1;
      for(int o=0;o<N;o++) if(comp[o]<0){ unsigned st=1u<<o, seen=st; comp[o]=o;
        while(st){ int v=__builtin_ctz(st); st&=st-1; unsigned nx=nb[v]&~seen; seen|=nx; st|=nx;
          for(unsigned t=nx;t;t&=t-1) comp[__builtin_ctz(t)]=o; } }
      long long total=0; int nvalid=0; int cstar=-2; int firstT[3]={0};
      for(int a=0;a<N;a++) for(int b=a+1;b<N;b++) for(int cc=b+1;cc<N;cc++){
        unsigned Tm=(1u<<a)|(1u<<b)|(1u<<cc);
        int rest[16], k=0, ok=1;
        for(int o=0;o<N;o++) if(!(Tm>>o&1)){ rest[k++]=o;
          int outdeg=__builtin_popcount(nb[o]&~Tm);
          if(mu[o]<0||mu[o]>outdeg) ok=0; }
        if(!ok) continue;
        if(modeb){
          int T3[3]={a,b,cc}; int v[16]={0}; int hasin=0;
          v[lastv]+=1; v[0]-=1;
          for(int j=1;j<=r;j++){ int p=par[j+1], ch=j+1, s=states[j-1];
            int pin=Tm>>p&1, cin=Tm>>ch&1;
            if(s==2&&pin&&cin) hasin=1;
            if(s==1){ v[p]+=1; v[ch]-=1; }
            if(s==2&&pin&&!cin){ v[p]+=1; v[ch]-=1; } }
          if(!hasin){ int nz[3],m=0; for(int i=0;i<3;i++) if(v[T3[i]]) nz[m++]=v[T3[i]];
            if(m==0) continue; if(m==2&&nz[0]==-nz[1]) continue; }
        }
        /* DP over placed subsets of rest (from the top) */
        int idx[16]; for(int i=0;i<k;i++) idx[rest[i]]=i;
        unsigned onb[16]; for(int i=0;i<k;i++){ unsigned m=0; for(unsigned t=nb[rest[i]]&~Tm;t;t&=t-1) m|=1u<<idx[__builtin_ctz(t)]; onb[i]=m; }
        int full=(1<<k)-1; memset(dp,0,sizeof(long long)<<k); dp[0]=1;
        for(int pl=0;pl<full;pl++){ if(!dp[pl]) continue;
          for(int i=0;i<k;i++) if(!(pl>>i&1)){
            int below=__builtin_popcount(onb[i]&~pl&~(1u<<i));
            if(below==mu[rest[i]]) dp[pl|1<<i]+=dp[pl]; } }
        long long cnt=dp[full];
        if(!cnt) continue;
        total+=cnt; nvalid++;
        /* structural checks */
        if((neg & ~Tm)) viol1++;                         /* Neg subset T */
        if(nneg==1){
          if(a!=0){ viol2++; continue; }
          if(!(nb[b]>>cc&1)){ viol2++; continue; }        /* uw in F */
          if(cstar==-2) cstar=comp[b]; else if(cstar!=comp[b]) viol3++;
        }
        if(nneg==2){
          if(nvalid>1) viol4++;
          int z=-1; for(int o=1;o<N;o++) if(neg>>o&1) z=o;
          int x = (a==z)?-1: a; int T3[3]={a,b,cc}; for(int i=0;i<3;i++) if(T3[i]!=0&&T3[i]!=z) x=T3[i];
          if(!(z>=1 && !spine[z] && linpar[z] && par[z]==x)) viol5++;
        }
      }
      if(nneg==1 && cstar>=0){       /* tau == 1 on spine of C* */
        for(int v=1; v<N; v++) if(spine[v] && comp[v]==cstar && kap[v]-hingeleafch[v]!=1) viol3++;
      }
      if(total>best){best=total;bestS=S;bestSt=code;}
      if(nneg<8 && total>bestNeg[nneg]) bestNeg[nneg]=total;
      if(nneg<8) hist_valid_by_neg[nneg]+= nvalid?1:0;
    }
  }
  printf("N=%d mode=%s units=%lld (N-3)!=%lld\n",N,modeb?"a+b'":"a",nunits,F);
  printf("max total=%lld  W=%.6f  at S=%d stcode=%lld\n",best,(double)best/F,bestS,bestSt);
  for(int i=1;i<5;i++) printf("|Neg|=%d: max W=%.6f, units with some valid T=%lld\n",i,(double)bestNeg[i]/F,hist_valid_by_neg[i]);
  printf("violations: Neg not in T=%lld, CaseI T shape=%lld, CaseI one-comp/tau=%lld, CaseII >1 triple=%lld, CaseII x!=parent(z)=%lld\n",viol1,viol2,viol3,viol4,viol5);
  return 0;
}
