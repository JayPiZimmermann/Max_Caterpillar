// Exhaustive search for the smallest "top-good" set of caterpillar units
// (a braid-linear combination, i.e. no kinks inside open braid cells, with
// D_[N] != 0).  Every caterpillar expansion of max_N contains such a set, so
// the minimum m_N is a lower bound for s_N.  (h5-growth branch, see README.md)
//
// Same branching as edfs2.cpp (complete for minimal good sets = circuits), plus
//  * root orbits processed in a user-given order; the D-active units of every
//    orbit processed earlier are excluded (WLOG by S_N symmetry);
//  * at the first branching level, candidates that are images of an earlier
//    candidate under the stabilizer of the root are skipped (the stabilizer
//    fixes C={root} and the S_N-invariant exclusion set);
//  * rigorous goodness test: "not good mod P1 and mod P2" implies "not good
//    over Q" because every nonzero minor of [KINK_C; D] is < P1*P2 in absolute
//    value (Hadamard: product of column norms; checked at start for MAXS).
// usage: edfs3 data/edfs_N.txt maxsize time_limit_s minsize order(comma list|all) 
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;

int n, G, nS;
vector<vector<int>> D;
vector<vector<pair<int,int>>> grp, ug;
vector<vector<int>> perm;
vector<int> inC, excl, cntg, C;
ll nodes = 0; int MAXS; double TL;
chrono::steady_clock::time_point T0;
bool found = false; vector<int> best;
const ll P1 = 2147483629LL, P2 = 2147483587LL;
vector<int> stabRoot; // list of perm indices fixing the root
int depthRoot = 1;

ll pw(ll a, ll e, ll p) { ll r = 1; a %= p; if (a < 0) a += p; while (e) { if (e & 1) r = r * a % p; a = a * a % p; e >>= 1; } return r; }

bool good_p(ll p) {
    int m = C.size();
    vector<vector<ll>> basis; vector<int> pivc;
    auto reduce = [&](vector<ll>& v) {
        for (size_t b = 0; b < basis.size(); b++) { int c = pivc[b];
            if (v[c]) { ll f = v[c]; for (int j = 0; j < m; j++) v[j] = ((v[j] - f * basis[b][j]) % p + p) % p; } }
    };
    auto add = [&](vector<ll>& v) {
        reduce(v); int c = -1; for (int j = 0; j < m; j++) if (v[j]) { c = j; break; }
        if (c < 0) return false; ll inv = pw(v[c], p - 2, p);
        for (int j = 0; j < m; j++) v[j] = v[j] * inv % p; basis.push_back(v); pivc.push_back(c); return true;
    };
    set<int> gs; for (int u : C) for (auto& pr : ug[u]) gs.insert(pr.first);
    for (int g : gs) {
        vector<ll> v(m, 0);
        for (int i = 0; i < m; i++) for (auto& pr : ug[C[i]]) if (pr.first == g) v[i] = ((ll)pr.second % p + p) % p;
        add(v); if ((int)basis.size() == m) return false;
    }
    vector<ll> d(m); for (int i = 0; i < m; i++) d[i] = ((ll)D[C[i]][nS - 1] % p + p) % p;
    reduce(d); for (int j = 0; j < m; j++) if (d[j]) return true; return false;
}
bool good() { return good_p(P1) || good_p(P2); }
bool timeout() { return chrono::duration<double>(chrono::steady_clock::now() - T0).count() > TL; }
void addu(int u) { inC[u] = 1; C.push_back(u); for (auto& pr : ug[u]) cntg[pr.first]++; }
void remu(int u) { inC[u] = 0; C.pop_back(); for (auto& pr : ug[u]) cntg[pr.first]--; }

void dfs() {
    if (found) return;
    nodes++;
    if ((nodes & 0xFFFF) == 0 && timeout()) throw runtime_error("timeout");
    int m = C.size();
    bool atRoot = (m == 1);
    vector<int> singles;
    { set<int> seen; for (int u : C) for (auto& pr : ug[u]) if (cntg[pr.first] == 1 && !seen.count(pr.first)) { seen.insert(pr.first); singles.push_back(pr.first); } }
    vector<int> cand;
    if (!singles.empty()) {
        vector<pair<int,int>> sc;
        for (int g : singles) { int c = 0; for (auto& pr : grp[g]) if (!inC[pr.first] && !excl[pr.first]) c++; if (c == 0) return; sc.push_back({c, g}); }
        sort(sc.begin(), sc.end());
        vector<char> used(n, 0); int lb = 0;
        for (auto& q : sc) { int g = q.second; bool dis = true;
            for (auto& pr : grp[g]) { int u = pr.first; if (!inC[u] && !excl[u] && used[u]) { dis = false; break; } }
            if (dis) { lb++; for (auto& pr : grp[g]) { int u = pr.first; if (!inC[u] && !excl[u]) used[u] = 1; } } }
        if (m + lb > MAXS) return;
        int g = sc[0].second;
        for (auto& pr : grp[g]) if (!inC[pr.first] && !excl[pr.first]) cand.push_back(pr.first);
    } else {
        if (good()) { found = true; best = C; return; }
        if (m >= MAXS) return;
        set<int> nb;
        for (int u : C) for (auto& pr : ug[u]) for (auto& q : grp[pr.first]) if (!inC[q.first] && !excl[q.first]) nb.insert(q.first);
        cand.assign(nb.begin(), nb.end());
    }
    vector<int> ex; set<int> seenImg;
    for (int u : cand) {
        if (atRoot && seenImg.count(u)) continue;   // stabilizer image of an earlier candidate
        addu(u); dfs(); remu(u);
        if (found) return;
        excl[u] = 1; ex.push_back(u);
        if (atRoot) for (int p : stabRoot) seenImg.insert(perm[p][u]);
    }
    for (int u : ex) excl[u] = 0;
}

int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r");
    MAXS = atoi(argv[2]); TL = argc > 3 ? atof(argv[3]) : 1e18;
    int MINS = argc > 4 ? atoi(argv[4]) : 1;
    string ord = argc > 5 ? argv[5] : "all";
    if (fscanf(f, "%d %d %d", &n, &G, &nS) != 3) return 1;
    D.assign(n, vector<int>(nS));
    for (int u = 0; u < n; u++) for (int s = 0; s < nS; s++) if (fscanf(f, "%d", &D[u][s]) != 1) return 1;
    grp.resize(G); ug.resize(n);
    for (int g = 0; g < G; g++) { int sz; if (fscanf(f, "%d", &sz) != 1) return 1;
        for (int i = 0; i < sz; i++) { int u, l; if (fscanf(f, "%d %d", &u, &l) != 2) return 1; grp[g].push_back({u, l}); ug[u].push_back({g, l}); } }
    int np; if (fscanf(f, "%d", &np) != 1) return 1;
    perm.assign(np, vector<int>(n));
    for (int p = 0; p < np; p++) for (int u = 0; u < n; u++) if (fscanf(f, "%d", &perm[p][u]) != 1) return 1;
    fclose(f);
    // Hadamard check for rigor of the two-prime test
    long double mx = 0;
    for (int u = 0; u < n; u++) { long double s = (long double)D[u][nS-1] * D[u][nS-1]; for (auto& pr : ug[u]) s += (long double)pr.second * pr.second; mx = max(mx, sqrtl(s)); }
    long double hb = powl(max(mx, (long double)1), MAXS);
    printf("max column norm %.3Lf, Hadamard bound %.3Le vs P1*P2 %.3Le : %s\n", mx, hb, (long double)P1 * P2, hb < (long double)P1 * P2 ? "RIGOROUS" : "NOT RIGOROUS");
    inC.assign(n, 0); excl.assign(n, 0); cntg.assign(G, 0);
    vector<int> orb(n, -1), reps;
    for (int u = 0; u < n; u++) if (D[u][nS - 1] != 0 && orb[u] < 0) { int id = reps.size(); reps.push_back(u); for (int p = 0; p < np; p++) orb[perm[p][u]] = id; }
    vector<int> order;
    if (ord == "all") for (size_t i = 0; i < reps.size(); i++) order.push_back(i);
    else { stringstream ss(ord); string t; while (getline(ss, t, ',')) order.push_back(stoi(t)); }
    printf("n %d groups %d D-active orbits %zu order", n, G, reps.size()); for (int o : order) printf(" %d", o); printf("\n");
    for (size_t i = 0; i < reps.size(); i++) { int st = 0, osz = 0; for (int p = 0; p < np; p++) if (perm[p][reps[i]] == reps[i]) st++; for (int u = 0; u < n; u++) if (orb[u] == (int)i) osz++; printf("  orbit %zu rep %d size %d stab %d\n", i, reps[i], osz, st); }
    fflush(stdout);
    T0 = chrono::steady_clock::now();
    int maxs = MAXS;
    // order positions: orbit order[k] excludes D-active units of orbits order[0..k-1]
    // NOTE: completeness requires the full list of orbits when the order is a permutation;
    // partial lists are only valid if the omitted orbits come AFTER (they are not excluded).
    try {
        for (int s = MINS; s <= maxs; s++) {
            MAXS = s; ll before = nodes;
            for (size_t k = 0; k < order.size() && !found; k++) {
                int i = order[k];
                vector<int> pos(reps.size(), -1); for (size_t j = 0; j < k; j++) pos[order[j]] = 1;
                for (int u = 0; u < n; u++) excl[u] = (orb[u] >= 0 && pos[orb[u]] == 1) ? 1 : 0;
                stabRoot.clear(); for (int p = 0; p < np; p++) if (perm[p][reps[i]] == reps[i]) stabRoot.push_back(p);
                ll b0 = nodes;
                addu(reps[i]); dfs(); remu(reps[i]);
                double t = chrono::duration<double>(chrono::steady_clock::now() - T0).count();
                printf("  size<=%d orbit %d done nodes %lld t=%.1fs%s\n", s, i, nodes - b0, t, found ? " FOUND" : ""); fflush(stdout);
            }
            double t = chrono::duration<double>(chrono::steady_clock::now() - T0).count();
            if (found) { printf("FOUND size %zu (max %d) nodes %lld t=%.1fs units:", best.size(), s, nodes, t); for (int u : best) printf(" %d", u); printf("\n"); return 0; }
            printf("EXHAUSTED size <= %d : no good set; nodes %lld (this level %lld) t=%.1fs\n", s, nodes, nodes - before, t); fflush(stdout);
        }
    } catch (runtime_error&) { printf("TIMEOUT at size %d nodes %lld\n", MAXS, nodes); }
    return 0;
}
