/* Round 4. EXACT (for each enumerated weight graph) / exhaustive over a weight box.
 * For a real symmetric weight matrix c on n vertices and a target vector D, an order
 * (bottom..top) of the n vertices is VALID if every vertex o has c(o, below(o)) = D_o.
 * qmax(c) = max over D of (#valid orders)/n! = (max multiplicity of the vector
 * s(order) = (c(o,below(o)))_o)/n!.
 * Enumerates all c with integer weights in [-W,W] (n <= 5 exhaustive) and reports the
 * maximum qmax for each matching number nu of the support graph.
 * Usage: qmax n W            (exhaustive)
 *        qmax n W samples seed  (random sampling, for n = 6,7)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, W, np;
static int pi_[64][2];
static int perms[5040][7];
static int nperm;

static void genperm(int *a, int k) {
    if (k == n) { memcpy(perms[nperm++], a, sizeof(int) * n); return; }
    for (int i = k; i < n; i++) {
        int t = a[k]; a[k] = a[i]; a[i] = t;
        genperm(a, k + 1);
        t = a[k]; a[k] = a[i]; a[i] = t;
    }
}

static int nu_of(int *w) { /* maximum matching size of support, brute force over edge subsets */
    int best = 0;
    /* greedy over all orderings is overkill; do recursive */
    int used = 0;
    int rec(int e, int usedmask) {
        if (e == np) return 0;
        int b = rec(e + 1, usedmask);
        if (w[e] && !(usedmask >> pi_[e][0] & 1) && !(usedmask >> pi_[e][1] & 1)) {
            int c = 1 + rec(e + 1, usedmask | 1 << pi_[e][0] | 1 << pi_[e][1]);
            if (c > b) b = c;
        }
        return b;
    }
    (void)used;
    best = rec(0, 0);
    return best;
}

static int cmpvec(const void *a, const void *b) { return memcmp(a, b, sizeof(int) * 8); }

static double qmax(int *w, int *bestvec) {
    int C[8][8] = {{0}};
    for (int e = 0; e < np; e++) { C[pi_[e][0]][pi_[e][1]] = w[e]; C[pi_[e][1]][pi_[e][0]] = w[e]; }
    static int vecs[5040][8];
    for (int p = 0; p < nperm; p++) {
        int *o = perms[p];
        memset(vecs[p], 0, sizeof(int) * 8);
        for (int i = 0; i < n; i++) {
            int s = 0;
            for (int j = 0; j < i; j++) s += C[o[i]][o[j]];
            vecs[p][o[i]] = s;
        }
    }
    qsort(vecs, nperm, sizeof(int) * 8, cmpvec);
    int best = 0, run = 1, bi = 0;
    for (int p = 1; p <= nperm; p++) {
        if (p < nperm && !cmpvec(vecs[p], vecs[p - 1])) run++;
        else { if (run > best) { best = run; bi = p - 1; } run = 1; }
    }
    if (bestvec) memcpy(bestvec, vecs[bi], sizeof(int) * 8);
    return (double)best / nperm;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); W = atoi(argv[2]);
    long samples = argc > 3 ? atol(argv[3]) : 0;
    unsigned seed = argc > 4 ? atoi(argv[4]) : 1;
    np = 0;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) { pi_[np][0] = i; pi_[np][1] = j; np++; }
    int a[8]; for (int i = 0; i < n; i++) a[i] = i;
    nperm = 0; genperm(a, 0);
    double best[8] = {0}; int bw[8][64]; int bv[8][8];
    int w[64];
    long total = 1; for (int e = 0; e < np; e++) total *= (2 * W + 1);
    long iters = samples ? samples : total;
    srand(seed);
    for (long it = 0; it < iters; it++) {
        if (samples) { for (int e = 0; e < np; e++) w[e] = (rand() % 3 == 0) ? 0 : (rand() % (2 * W + 1)) - W; }
        else { long x = it; for (int e = 0; e < np; e++) { w[e] = (int)(x % (2 * W + 1)) - W; x /= (2 * W + 1); } }
        int nu = nu_of(w);
        int vec[8];
        double q = qmax(w, vec);
        if (q > best[nu] + 1e-12) { best[nu] = q; memcpy(bw[nu], w, sizeof(int) * np); memcpy(bv[nu], vec, sizeof(int) * 8); }
    }
    for (int nu = 0; nu <= n / 2; nu++) {
        printf("n %d W %d nu %d qmax %.6f  weights", n, W, nu, best[nu]);
        for (int e = 0; e < np; e++) if (bw[nu][e]) printf(" %d%d:%d", pi_[e][0], pi_[e][1], bw[nu][e]);
        printf("  D");
        for (int i = 0; i < n; i++) printf(" %d", bv[nu][i]);
        printf("\n");
    }
    return 0;
}
