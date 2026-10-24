// Greedy maximal infeasible extension (mod p) for benders2.py.
// stdin: r n ; matrix B (r x n, row-major, residues) ; t (r) ; then queries:
//   m k_1..k_m  (K) followed by n numbers (order)   -> prints "F" if t in span(K)
//   else "I c u_1..u_c" listing K' (maximal infeasible superset).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long ull;
typedef unsigned int ui;
static const ull P = 2147483629ULL;
ull pw(ull a, ull e) { ull r = 1; a %= P; while (e) { if (e & 1) r = r * a % P; a = a * a % P; e >>= 1; } return r; }
int r, n;
vector<ui> B0, t0;
int main() {
    if (scanf("%d %d", &r, &n) != 2) return 1;
    B0.resize((size_t)r * n); t0.resize(r);
    for (size_t i = 0; i < (size_t)r * n; i++) { unsigned v; if (scanf("%u", &v) != 1) return 1; B0[i] = v; }
    for (int i = 0; i < r; i++) { unsigned v; if (scanf("%u", &v) != 1) return 1; t0[i] = v; }
    // column-major working copy for cache efficiency: col[u][i]
    vector<ui> C((size_t)n * r);
    int m;
    while (scanf("%d", &m) == 1) {
        vector<int> K(m), order(n);
        for (int i = 0; i < m; i++) if (scanf("%d", &K[i]) != 1) return 1;
        for (int i = 0; i < n; i++) if (scanf("%d", &order[i]) != 1) return 1;
        for (int u = 0; u < n; u++) for (int i = 0; i < r; i++) C[(size_t)u * r + i] = B0[(size_t)i * n + u];
        vector<ui> tr = t0;
        vector<char> alive(n, 1);
        // basis: list of (pivot row, normalized column vector) ; we reduce lazily per column
        vector<int> piv; vector<vector<ui>> bas;
        auto reduce = [&](ui* v) {
            for (size_t b = 0; b < bas.size(); b++) {
                ull f = v[piv[b]];
                if (!f) continue;
                const ui* w = bas[b].data();
                for (int i = 0; i < r; i++) if (w[i]) v[i] = (ui)((v[i] + (P - f) * w[i]) % P);
            }
        };
        auto addvec = [&](vector<ui> v) -> bool {
            // v already reduced
            int i0 = -1; for (int i = 0; i < r; i++) if (v[i]) { i0 = i; break; }
            if (i0 < 0) return false;
            ull f = pw(v[i0], P - 2);
            for (int i = 0; i < r; i++) v[i] = (ui)(v[i] * f % P);
            // keep basis fully reduced w.r.t. new pivot? not needed for correctness of reduce order:
            // reduce applies b in insertion order; new vectors are reduced by old ones, but old ones
            // may have nonzero at new pivot. Process: reduce v by all, then eliminate new pivot from old.
            for (size_t b = 0; b < bas.size(); b++) {
                ull g = bas[b][i0];
                if (!g) continue;
                for (int i = 0; i < r; i++) if (v[i]) bas[b][i] = (ui)((bas[b][i] + (P - g) * v[i]) % P);
            }
            piv.push_back(i0); bas.push_back(v);
            return true;
        };
        for (int u : K) {
            vector<ui> v(C.begin() + (size_t)u * r, C.begin() + (size_t)(u + 1) * r);
            reduce(v.data());
            addvec(v);
            alive[u] = 0;
        }
        reduce(tr.data());
        bool tz = true; for (int i = 0; i < r; i++) if (tr[i]) { tz = false; break; }
        if (tz) { printf("F\n"); fflush(stdout); continue; }
        vector<int> Kp = K;
        for (int u : order) {
            if (!alive[u]) continue;
            alive[u] = 0;
            vector<ui> v(C.begin() + (size_t)u * r, C.begin() + (size_t)(u + 1) * r);
            reduce(v.data());
            int i0 = -1; for (int i = 0; i < r; i++) if (v[i]) { i0 = i; break; }
            if (i0 < 0) { Kp.push_back(u); continue; }
            ull f = (ull)tr[i0] * pw(v[i0], P - 2) % P;
            bool par = true;
            for (int i = 0; i < r; i++) if ((tr[i] + (P - f) * v[i]) % P != 0) { par = false; break; }
            if (par) continue;
            Kp.push_back(u);
            addvec(v);
            reduce(tr.data());
        }
        printf("I %zu", Kp.size());
        for (int u : Kp) printf(" %d", u);
        printf("\n"); fflush(stdout);
    }
    return 0;
}
