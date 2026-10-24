/* Exhaustive check of the per-unit lemma (unified.md) for all forests on n vertices
   (stdin: edge lists from unified_exh.py) and all kappa in {-1,...,deg+1}.
   Delta = max(2, max omega), y = 1/(2Delta+2).  Checks W = sum_T y^|T| q(T) <= 1 and
   reports max W and max_m (sum_{|T|=m} q(T)) / b^m.  Also reports the same with
   Delta replaced by the out-leaf parameter s + 1 (out-leaf class, base 2s+4). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int n, ne, ea[16], eb[16], adj[8], deg[8], kap[8];
double fact[9];
double W_at(double y, double *perm_m) {
  double W = 0; for (int m = 0; m <= n; m++) perm_m[m] = 0;
  for (int T = 0; T < (1 << n); T++) {
    int ok = 1;
    for (int t = 0; t < n && ok; t++) if (T >> t & 1) if (!(adj[t] & T) && kap[t] == 0) ok = 0;
    if (!ok) continue;
    int O[8], no = 0, kp[8], idx[8];
    for (int o = 0; o < n; o++) if (!(T >> o & 1)) {
      kp[no] = kap[o] - __builtin_popcount(adj[o] & T); if (kp[no] < 0) ok = 0;
      idx[o] = no; O[no++] = o; }
    if (!ok) continue;
    static double f[256]; for (int S = 0; S < (1 << no); S++) f[S] = 0; f[0] = 1;
    int nadj[8];
    for (int i = 0; i < no; i++) { nadj[i] = 0; for (int j = 0; j < no; j++) if (adj[O[i]] >> O[j] & 1) nadj[i] |= 1 << j; }
    for (int S = 0; S < (1 << no); S++) { if (f[S] == 0) continue;
      for (int i = 0; i < no; i++) if (!(S >> i & 1) && __builtin_popcount(nadj[i] & S) == kp[i]) f[S | 1 << i] += f[S]; }
    double c = f[(1 << no) - 1]; if (c == 0) continue;
    int m = n - no; double q = c / fact[no];
    W += pow(y, m) * q; perm_m[m] += q;
  }
  return W;
}
int main() {
  fact[0] = 1; for (int i = 1; i < 9; i++) fact[i] = fact[i - 1] * i;
  double maxW = 0, maxR = 0, maxW2 = 0; long inst = 0;
  while (scanf("%d", &ne) == 1) {
    n = 0; for (int i = 0; i < 8; i++) adj[i] = 0;
    for (int i = 0; i < ne; i++) { scanf("%d %d", &ea[i], &eb[i]); adj[ea[i]] |= 1 << eb[i]; adj[eb[i]] |= 1 << ea[i]; }
    n = getenv("NV") ? atoi(getenv("NV")) : 6;
    for (int v = 0; v < n; v++) deg[v] = __builtin_popcount(adj[v]);
    int lo[8], hi[8]; for (int v = 0; v < n; v++) { lo[v] = -1; hi[v] = deg[v] + 1; kap[v] = lo[v]; }
    while (1) {
      int omega = 0, s = 0;
      for (int v = 0; v < n; v++) { int ol = 0, trunk = 0;
        for (int u = 0; u < n; u++) if (adj[v] >> u & 1) { if (deg[u] == 1 && kap[u] == 1) ol++; if (deg[u] >= 2) trunk = 1; }
        if (ol + trunk > omega) omega = ol + trunk; if (ol > s) s = ol; }
      int D = omega < 2 ? 2 : omega; double b = 2 * D + 2, pm[9];
      double W = W_at(1 / b, pm); inst++;
      if (W > maxW) maxW = W;
      if (W > 1 + 1e-12) { printf("FAIL W=%g kappa:", W); for (int v = 0; v < n; v++) printf(" %d", kap[v]); printf("\n"); }
      for (int m = 3; m <= n; m++) { double r = pm[m] / pow(b, m); if (r > maxR) maxR = r; }
      int D2 = s + 1 < 2 ? 2 : s + 1; double W2 = W_at(1.0 / (2 * D2 + 2), pm); if (W2 > maxW2) maxW2 = W2;
      if (W2 > 1 + 1e-12) printf("FAIL2\n");
      int v = 0; while (v < n && kap[v] == hi[v]) { kap[v] = lo[v]; v++; } if (v == n) break; kap[v]++;
    }
  }
  printf("instances %ld  max W %.6f  max_m ratio %.6f  max W (out-leaf, base 2s+4) %.6f\n", inst, maxW, maxR, maxW2);
  return 0;
}
