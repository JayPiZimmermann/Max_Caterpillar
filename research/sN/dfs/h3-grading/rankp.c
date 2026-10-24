/* Incremental rank modulo p = 2^31-1 of a sequence of vectors.
   Input (binary, little endian): int64 nvec, int64 dim, int64 nbreak, int64 breaks[nbreak],
   then nvec*dim int64 entries already reduced to [0,p).
   Output: for every break b (a prefix length), the rank of the first b vectors.
   Reduction: basis vectors kept in insertion order, each reduced against all earlier ones,
   so sequential elimination is exact modulo p.  A rank mod p is a lower bound for the
   rank over Q of the integer vectors. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define P 2147483647ULL
static uint64_t pw(uint64_t a, uint64_t e){uint64_t r=1;a%=P;while(e){if(e&1)r=r*a%P;a=a*a%P;e>>=1;}return r;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb"); int64_t nvec,dim,nb; fread(&nvec,8,1,f);fread(&dim,8,1,f);fread(&nb,8,1,f);
  int64_t*br=malloc(8*nb); fread(br,8,nb,f);
  uint64_t*B=malloc(sizeof(uint64_t)*dim*(dim<nvec?dim:nvec)); int64_t*piv=malloc(8*dim); int64_t r=0;
  uint64_t*v=malloc(8*dim); int64_t bi=0;
  while(bi<nb && br[bi]==0){printf("0 0\n");bi++;}
  for(int64_t k=0;k<nvec;k++){
    fread(v,8,dim,f);
    for(int64_t i=0;i<r;i++){uint64_t c=v[piv[i]]; if(!c)continue; uint64_t m=P-c; uint64_t*b=B+i*dim;
      for(int64_t j=0;j<dim;j++){ v[j]=(v[j]+m*b[j])%P; } }
    int64_t p=-1; for(int64_t j=0;j<dim;j++) if(v[j]){p=j;break;}
    if(p>=0){ uint64_t inv=pw(v[p],P-2); uint64_t*b=B+r*dim; for(int64_t j=0;j<dim;j++) b[j]=v[j]*inv%P; piv[r]=p; r++; }
    while(bi<nb && br[bi]<=k+1){ printf("%lld %lld\n",(long long)br[bi],(long long)r); bi++; }
  }
  while(bi<nb){printf("%lld %lld\n",(long long)br[bi],(long long)r);bi++;}
  return 0;}
