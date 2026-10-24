/* Evaluate Young-symmetrized orbit sums modulo p = 2^31-1.
   Input file (int64 little endian):
     N, nfam, then per family member: h[N], m, pairs (i,j) * m   (variable length)
     ncols, then per column: len, (member index, sign) * len
     npts, X[npts*N]
     ng, then per group element: sign, perm[N]   (point y = x o perm: y_i = x_{perm[i]})
   Output file: ncols*npts int64 values in [0,p): row c = column c evaluated at the points. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define P 2147483647LL
static int64_t rd(FILE*f){int64_t v; if(fread(&v,8,1,f)!=1){fprintf(stderr,"read error\n");exit(1);} return v;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb"); int64_t N=rd(f), nf=rd(f);
  int64_t*H=malloc(8*N*nf); int64_t*mstart=malloc(8*(nf+1)); int64_t*pairs=malloc(8*2*nf*N); int64_t np_=0;
  for(int64_t k=0;k<nf;k++){ for(int64_t i=0;i<N;i++) H[k*N+i]=rd(f); int64_t m=rd(f); mstart[k]=np_;
    for(int64_t t=0;t<m;t++){pairs[2*np_]=rd(f);pairs[2*np_+1]=rd(f);np_++;} } mstart[nf]=np_;
  int64_t nc=rd(f); int64_t*cstart=malloc(8*(nc+1)); int64_t cap=1<<20,nm=0; int64_t*cm=malloc(8*cap),*cs=malloc(8*cap);
  for(int64_t c=0;c<nc;c++){int64_t L=rd(f); cstart[c]=nm; for(int64_t t=0;t<L;t++){ if(nm==cap){cap*=2;cm=realloc(cm,8*cap);cs=realloc(cs,8*cap);} cm[nm]=rd(f);cs[nm]=rd(f);nm++;}} cstart[nc]=nm;
  int64_t npts=rd(f); int64_t*X=malloc(8*npts*N); for(int64_t i=0;i<npts*N;i++) X[i]=rd(f);
  int64_t ng=rd(f); int64_t*gs=malloc(8*ng); int64_t*gp=malloc(8*ng*N);
  for(int64_t g=0;g<ng;g++){gs[g]=rd(f); for(int64_t i=0;i<N;i++) gp[g*N+i]=rd(f);}
  fclose(f);
  /* permuted points Y[(g*npts+p)*N+i] */
  int64_t*Y=malloc(8*ng*npts*N);
  for(int64_t g=0;g<ng;g++) for(int64_t p=0;p<npts;p++) for(int64_t i=0;i<N;i++) Y[(g*npts+p)*N+i]=X[p*N+gp[g*N+i]];
  int64_t*out=malloc(8*nc*npts);
  #pragma omp parallel for schedule(dynamic,4)
  for(int64_t c=0;c<nc;c++){
    for(int64_t p=0;p<npts;p++){
      __int128 acc=0;
      for(int64_t t=cstart[c];t<cstart[c+1];t++){ int64_t k=cm[t]; int64_t s=cs[t]; const int64_t*h=H+k*N;
        int64_t sub=0;
        for(int64_t g=0;g<ng;g++){ const int64_t*y=Y+(g*npts+p)*N; int64_t a=0;
          for(int64_t i=0;i<N;i++) a+=h[i]*y[i];
          for(int64_t q=mstart[k];q<mstart[k+1];q++){ int64_t d=y[pairs[2*q]]-y[pairs[2*q+1]]; if(d>0) a+=d; }
          if(a>0) sub+= gs[g]*a; }
        acc += (__int128)s*sub; }
      int64_t v=(int64_t)(acc%P); if(v<0)v+=P; out[c*npts+p]=v; } }
  FILE*o=fopen(argv[2],"wb"); fwrite(out,8,nc*npts,o); fclose(o); return 0; }
