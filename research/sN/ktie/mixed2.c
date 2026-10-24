/* mixed2.c = mixed.c with MODE 1: count T when every t in T has v_t != 0 or lies on a pair of M(T) (local germ depends on all T coordinates: a rigorous superset of the units with nonzero class modulo functions missing a coordinate). */
/* Fast version of mixed.py: per-unit k-tie weight under the k-th mixed difference.
   Usage: ./mixed N k   (prints max_W numerator over (N-k)!, the argmax, and a histogram summary)
   Conventions identical to mixed.py / wk.py (identity labelling, apex 0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N, K, R, MODE;
static int h[16], nM, Mi[16], Mj[16];
static long long dp[1 << 14];
static int relu(int t) { return t > 0 ? t : 0; }
int main(int argc, char **argv) {
  N = atoi(argv[1]); K = atoi(argv[2]); MODE = argc > 3 ? atoi(argv[3]) : 0; R = N - 2;
  long long fact = 1; for (int i = 2; i <= N - K; i++) fact *= i;
  long long best = 0; int bestS = 0; int bestst[16];
  long long nunits = 0;
  int pw3 = 1; for (int i = 0; i < R; i++) pw3 *= 3;
  long long hist[4096]; memset(hist, 0, sizeof hist);
  for (int S = 1; S < (1 << R); S++) {
    /* S as subset of 1..R, bit i-1 */
    int par[16], last = 0;
    for (int j = 1; j <= R; j++) {
      int p = 0; for (int i = 1; i < j; i++) if (S >> (i - 1) & 1) p = i;
      par[j] = p;
    }
    for (int i = 1; i <= R; i++) if (S >> (i - 1) & 1) last = i;
    last += 1;
    for (int code = 0; code < pw3; code++) {
      int st[16], c = code;
      for (int j = 1; j <= R; j++) { st[j] = c % 3; c /= 3; }
      memset(h, 0, sizeof h); nM = 0;
      h[last]++; h[0]--;
      for (int j = 1; j <= R; j++) {
        int a = par[j] + 1, b = j + 1;
        if (st[j] == 1) { h[a]++; h[b]--; }
        if (st[j] == 2) {
          if (a > b) { h[a]++; h[b]--; int t = a; a = b; b = t; }
          Mi[nM] = a; Mj[nM] = b; nM++;
        }
      }
      if (nM == 0) { int np = 0, nn = 0, nz = 0; for (int o = 0; o < N; o++) { if (h[o] == 1) np++; else if (h[o] == -1) nn++; else if (h[o] == 0) nz++; }
        if (np == 1 && nn == 1 && nz == N - 2) continue; }
      nunits++;
      int mu[16], deg[16], nb[16]; /* nb: bitmask of F-neighbours */
      for (int o = 0; o < N; o++) { mu[o] = -h[o]; deg[o] = 0; nb[o] = 0; }
      for (int m = 0; m < nM; m++) { mu[Mj[m]]++; deg[Mi[m]]++; deg[Mj[m]]++; nb[Mi[m]] |= 1 << Mj[m]; nb[Mj[m]] |= 1 << Mi[m]; }
      int must = 0; for (int o = 0; o < N; o++) if (mu[o] < 0 || mu[o] > deg[o]) must |= 1 << o;
      long long W = 0;
      for (int T = 0; T < (1 << N); T++) {
        if (__builtin_popcount(T) != K) continue;
        if ((T & must) != must) continue;
        int pos[16], tl[16], n = 0;
        for (int o = 0; o < N; o++) if (T >> o & 1) { pos[o] = n; tl[n++] = o; }
        int v[16]; for (int a = 0; a < K; a++) v[a] = h[tl[a]];
        int li[16], lj[16], nl = 0;
        for (int m = 0; m < nM; m++) {
          int a = Mi[m], b = Mj[m], ia = T >> a & 1, ib = T >> b & 1;
          if (ia && ib) { li[nl] = pos[a]; lj[nl] = pos[b]; nl++; }
          else if (ia) v[pos[a]]++;
        }
        long long lam = 0;
        for (int z = 0; z < (1 << K); z++) {
          int s = 0; for (int a = 0; a < K; a++) if (z >> a & 1) s += v[a];
          for (int l = 0; l < nl; l++) s += relu((z >> li[l] & 1) - (z >> lj[l] & 1));
          int g = relu(s);
          lam += ((K - __builtin_popcount(z)) & 1) ? -g : g;
        }
        if (MODE == 0 && lam == 0) continue;
        if (MODE == 1) { int inc = 0; for (int l = 0; l < nl; l++) inc |= (1 << li[l]) | (1 << lj[l]); int ok = 1; for (int a = 0; a < K; a++) if (!v[a] && !(inc >> a & 1)) ok = 0; if (!ok) continue; }
        /* count orders */
        int out[16], no = 0; for (int o = 0; o < N; o++) if (!(T >> o & 1)) out[no++] = o;
        int full = (1 << no) - 1;
        for (int P = 0; P <= full; P++) dp[P] = 0;
        dp[0] = 1;
        for (int P = 0; P < full; P++) {
          if (!dp[P]) continue;
          /* placed set in original labels */
          int placedL = 0; for (int x = 0; x < no; x++) if (P >> x & 1) placedL |= 1 << out[x];
          for (int x = 0; x < no; x++) {
            if (P >> x & 1) continue;
            int o = out[x];
            int below = __builtin_popcount(nb[o] & ~T & ~placedL & ~(1 << o));
            if (below == mu[o]) dp[P | 1 << x] += dp[P];
          }
        }
        W += dp[full];
      }
      long long hw = W * 8 / fact; if (hw > 4095) hw = 4095; hist[hw]++;
      if (W > best) { best = W; bestS = S; memcpy(bestst, st, sizeof st); }
    }
  }
  printf("N=%d k=%d units=%lld maxW = %lld/%lld = %.4f\n", N, K, nunits, best, fact, (double)best / fact);
  printf("  argmax S={"); for (int i = 1; i <= R; i++) if (bestS >> (i - 1) & 1) printf("%d,", i);
  printf("} states=("); for (int j = 1; j <= R; j++) printf("%d,", bestst[j]); printf(")\n");
  printf("  hist (8W -> units):"); for (int i = 0; i < 4096; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]); printf("\n");
  return 0;
}
