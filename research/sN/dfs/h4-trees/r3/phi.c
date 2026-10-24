/* Phi(C,e) for the P1 class (branch h4-trees, r3).
   Tree C on n vertices, e_o = kappa_o - deg(o) + 1 in {0,1} (e>=2 is dominated, see notes).
   Phi(x) = sum over S subset C satisfying (s) and validity of
            x^{|S| + sum_S e + c(C-S) - 1} * prod_{Q comp of C-S} h(Q, sink_Q)
   valid: every component Q of C-S has exactly one vertex with e=1 (its sink);
   h(Q,r) = prod_{v in Q} 1/|subtree_r(v)|  (heap-order probability).
   (s): t in S with no neighbour in S has kappa_t != 0, i.e. not (deg_t==1 && e_t==0).
   Modes:  ./phi max X1 X2 ...  < trees file : max over all e of Phi(x) for each x, with argmax
           ./phi G < lines "n nbr.. e.."      : print G_C coefficients q-sum by |S| (for cross-check)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 16
static int LOCAL = 0;
static int n, nbr[MAXN], deg[MAXN];
/* returns 0 if invalid, else fills exponent and weight */
static double subtree_h(int r, int p, int Omask, int *sz) {
  double w = 1; int s = 1;
  int m = nbr[r] & Omask;
  while (m) { int v = __builtin_ctz(m); m &= m - 1; if (v == p) continue;
    int s2; w *= subtree_h(v, r, Omask, &s2); s += s2; }
  *sz = s; return w / s;
}
static int eval_S(int S, const int *e, int *expo, double *w) {
  int full = (1 << n) - 1, O = full & ~S;
  for (int t = 0; t < n; t++) if ((S >> t & 1) && !(nbr[t] & S) && deg[t] == 1 && e[t] == 0) return 0;
  if (n == 1 && S == 1 && e[0] == 1) return 0; /* kappa = e - 1 = 0 */
  int seen = 0, comps = 0, ex = __builtin_popcount(S);
  for (int t = 0; t < n; t++) if (S >> t & 1) ex += e[t];
  double wt = 1;
  for (int v = 0; v < n; v++) if ((O >> v & 1) && !(seen >> v & 1)) {
    /* BFS component */
    int comp = 1 << v, frontier = 1 << v;
    while (frontier) { int nf = 0, f = frontier;
      while (f) { int u = __builtin_ctz(f); f &= f - 1; nf |= nbr[u] & O & ~comp; }
      comp |= nf; frontier = nf; }
    seen |= comp; comps++;
    int sinks = 0, r = -1;
    for (int u = 0; u < n; u++) if ((comp >> u & 1) && e[u] == 1) { sinks++; r = u; }
    if (sinks != 1) return 0;
    if (LOCAL) { for (int u = 0; u < n; u++) if (comp >> u & 1) wt /= (__builtin_popcount(nbr[u] & O) + e[u]); }
    else { int sz; wt *= subtree_h(r, -1, O, &sz); }
  }
  *expo = ex + comps - 1; *w = wt; return 1;
}
int main(int argc, char **argv) {
  if (argc >= 2 && !strcmp(argv[1], "G")) {
    while (scanf("%d", &n) == 1) {
      int e[MAXN];
      for (int i = 0; i < n; i++) { scanf("%d", &nbr[i]); deg[i] = __builtin_popcount(nbr[i]); }
      for (int i = 0; i < n; i++) scanf("%d", &e[i]);
      double g[MAXN + 1] = {0};
      for (int S = 0; S < (1 << n); S++) { int ex; double w; if (eval_S(S, e, &ex, &w)) g[__builtin_popcount(S)] += w; }
      for (int m = 0; m <= n; m++) printf("%.12g ", g[m]); printf("\n");
    }
    return 0;
  }
  if (getenv("LOCAL")) LOCAL = 1;
  int nx = argc - 2; double X[32]; for (int i = 0; i < nx; i++) X[i] = atof(argv[i + 2]);
  double best[32]; int bestE[32], bestT[32]; for (int i = 0; i < nx; i++) best[i] = -1;
  char line[4096]; int tid = 0;
  static int edges[MAXN][2];
  while (fgets(line, sizeof line, stdin)) {
    char *p = line; int k; n = strtol(p, &p, 10); if (n <= 0) continue;
    memset(nbr, 0, sizeof nbr);
    for (int i = 0; i < n - 1; i++) { int u = strtol(p, &p, 10), w = strtol(p, &p, 10); nbr[u] |= 1 << w; nbr[w] |= 1 << u; edges[i][0]=u; edges[i][1]=w; }
    for (int i = 0; i < n; i++) deg[i] = __builtin_popcount(nbr[i]);
    int E = 1 << n;
    double *bl = malloc(sizeof(double) * nx * E);
    #pragma omp parallel for schedule(dynamic, 16)
    for (int em = 0; em < E; em++) {
      int e[MAXN]; for (int i = 0; i < n; i++) e[i] = em >> i & 1;
      double coef[4 * MAXN + 2]; memset(coef, 0, sizeof coef);
      for (int S = 0; S < (1 << n); S++) { int ex; double w; if (eval_S(S, e, &ex, &w)) coef[ex] += w; }
      for (int i = 0; i < nx; i++) { double v = 0, xp = 1; for (int j = 0; j < 4 * MAXN + 2; j++) { v += coef[j] * xp; xp *= X[i]; } bl[i * E + em] = v; }
    }
    for (int i = 0; i < nx; i++) for (int em = 0; em < E; em++) if (bl[i * E + em] > best[i]) { best[i] = bl[i * E + em]; bestE[i] = em; bestT[i] = tid; }
    free(bl); tid++;
    (void)k;
  }
  for (int i = 0; i < nx; i++) printf("x=%g max Phi=%.10f tree#%d e-mask=%d\n", X[i], best[i], bestT[i], bestE[i]);
  return 0;
}
