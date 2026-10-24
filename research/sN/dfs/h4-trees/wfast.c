/* Per-unit locality counts for general tree units (branch h4-trees).
   stdin: lines "n nbr_0 .. nbr_{n-1} kappa_0 .. kappa_{n-1}" (nbr = bitmask of
   hinge neighbours).  stdout: per line, for m = 0..n, the integer
   c_m = sum over admissible T (|T| = m, condition (s)) of #orders of the
   outside satisfying (a).  w_m = c_m / (n-m)!.  Exact (64-bit counts). */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
static uint64_t dp[1 << 12];
int main(void) {
  int n;
  while (scanf("%d", &n) == 1) {
    int nbr[16], kap[16];
    for (int i = 0; i < n; i++) scanf("%d", &nbr[i]);
    for (int i = 0; i < n; i++) scanf("%d", &kap[i]);
    uint64_t c[17]; memset(c, 0, sizeof c);
    int full = (1 << n) - 1;
    for (int T = 0; T <= full; T++) {
      int m = __builtin_popcount(T), ok = 1;
      for (int t = 0; t < n && ok; t++)
        if ((T >> t & 1) && !(nbr[t] & T) && kap[t] == 0) ok = 0;
      for (int o = 0; o < n && ok; o++)
        if (!(T >> o & 1) && (kap[o] < 0 || kap[o] > __builtin_popcount(nbr[o]))) ok = 0;
      if (!ok) continue;
      /* dp over subsets P of outside already placed (as masks of full set incl. T) */
      int out = full & ~T;
      /* iterate submasks of out in increasing order */
      dp[0] = 1; /* index by compressed? use direct mask of out bits via sub enumeration */
      /* map: use array indexed by full mask (n <= 12) */
      static uint64_t D[1 << 12];
      for (int s = out;; s = (s - 1) & out) { D[s] = 0; if (!s) break; }
      D[0] = 1;
      /* increasing submask enumeration */
      for (int s = 0;; s = (s - out) & out) {
        uint64_t v = D[s];
        if (v) {
          int placed = s | T;
          int rem = out & ~s;
          while (rem) {
            int o = __builtin_ctz(rem); rem &= rem - 1;
            if (__builtin_popcount(nbr[o] & placed) == kap[o]) D[s | 1 << o] += v;
          }
        }
        if (s == out) break;
      }
      c[m] += D[out];
    }
    for (int m = 0; m <= n; m++) printf("%llu ", (unsigned long long)c[m]);
    printf("\n");
  }
  return 0;
}
