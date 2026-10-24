// Exhaustive search for the smallest D_[N]-active braid-linear combination
// (e_N, mode "top") among caterpillar units, by kink closure.
//
// A set C is "good" if some combination of the units in C has no kinks inside
// braid cells (KINK rows restricted to C vanish) and D_[N] != 0.  A minimal good
// set is a circuit: the solution is unique up to scale and all coefficients are
// nonzero, so every kink group meeting C meets it in >= 2 units, and C is
// connected in the group hypergraph (otherwise a component is good).
// Branching (complete for minimal good sets):
//   root: C contains a D-active unit; by S_N symmetry it is the representative
//         r_i of the i-th D-active orbit and no D-active unit of an earlier orbit;
//   a group meeting C in exactly one unit: branch on its other members
//         (exclusion chain);
//   closed C, not good: branch on units sharing a group with C (exclusion chain).
// Goodness test: rank over GF(p) for two primes; "good" if D_top is outside the
// row space of KINK_C for either prime (see README for the rigor caveat).
// usage: edfs2 data/edfs_N.txt maxsize time_limit_s minsize root_from root_to   (root orbit range [from,to))
// (copy of edfs.cpp restricted to a range of root orbits, for parallel runs)
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;

int n, G, nS;
vector<vector<int>> D;           // D[u][s]
vector<vector<pair<int,int>>> grp;  // group -> (u, lam)
vector<vector<pair<int,int>>> ug;   // unit -> (g, lam)
vector<vector<int>> perm;
int W;                            // bitset words
vector<vector<ull>> gbits;        // group member bitsets

vector<int> inC, excl, cntg;
vector<int> C;
ll nodes = 0;
int MAXS;
double TL;
chrono::steady_clock::time_point T0;
bool found = false;
vector<int> best;

const ll P1 = 2147483629LL, P2 = 2147483587LL;

ll pw(ll a, ll e, ll p) { ll r = 1; a %= p; if (a < 0) a += p; while (e) { if (e & 1) r = r * a % p; a = a * a % p; e >>= 1; } return r; }

bool good_p(ll p) {
    int m = C.size();
    // echelon basis of row space of KINK_C (vectors in F_p^m)
    vector<vector<ll>> basis; vector<int> pivc;
    auto reduce = [&](vector<ll>& v) {
        for (size_t b = 0; b < basis.size(); b++) {
            int c = pivc[b];
            if (v[c]) { ll f = v[c]; for (int j = 0; j < m; j++) v[j] = ((v[j] - f * basis[b][j]) % p + p) % p; }
        }
    };
    auto add = [&](vector<ll>& v) {
        reduce(v);
        int c = -1; for (int j = 0; j < m; j++) if (v[j]) { c = j; break; }
        if (c < 0) return false;
        ll inv = pw(v[c], p - 2, p);
        for (int j = 0; j < m; j++) v[j] = v[j] * inv % p;
        basis.push_back(v); pivc.push_back(c);
        return true;
    };
    // collect touched groups
    set<int> gs;
    for (int u : C) for (auto& pr : ug[u]) gs.insert(pr.first);
    for (int g : gs) {
        vector<ll> v(m, 0);
        for (int i = 0; i < m; i++) {
            for (auto& pr : ug[C[i]]) if (pr.first == g) v[i] = ((ll)pr.second % p + p) % p;
        }
        add(v);
        if ((int)basis.size() == m) return false;  // kernel trivial
    }
    vector<ll> d(m);
    for (int i = 0; i < m; i++) d[i] = ((ll)D[C[i]][nS - 1] % p + p) % p;
    reduce(d);
    for (int j = 0; j < m; j++) if (d[j]) return true;
    return false;
}
bool good() { return good_p(P1) || good_p(P2); }

bool timeout() {
    return chrono::duration<double>(chrono::steady_clock::now() - T0).count() > TL;
}

void addu(int u) { inC[u] = 1; C.push_back(u); for (auto& pr : ug[u]) cntg[pr.first]++; }
void remu(int u) { inC[u] = 0; C.pop_back(); for (auto& pr : ug[u]) cntg[pr.first]--; }

void dfs() {
    if (found) return;
    nodes++;
    if ((nodes & 0xFFFF) == 0 && timeout()) { throw runtime_error("timeout"); }
    int m = C.size();
    // singleton groups
    vector<int> singles;
    {
        set<int> seen;
        for (int u : C) for (auto& pr : ug[u]) if (cntg[pr.first] == 1 && !seen.count(pr.first)) { seen.insert(pr.first); singles.push_back(pr.first); }
    }
    if (!singles.empty()) {
        // candidates per singleton
        vector<pair<int,int>> sc; // (#cand, g)
        for (int g : singles) {
            int c = 0;
            for (auto& pr : grp[g]) if (!inC[pr.first] && !excl[pr.first]) c++;
            if (c == 0) return;
            sc.push_back({c, g});
        }
        sort(sc.begin(), sc.end());
        // disjoint packing lower bound
        vector<ull> used(W, 0); int lb = 0;
        for (auto& q : sc) {
            int g = q.second; bool dis = true;
            for (auto& pr : grp[g]) { int u = pr.first; if (!inC[u] && !excl[u] && (used[u >> 6] >> (u & 63) & 1)) { dis = false; break; } }
            if (dis) { lb++; for (auto& pr : grp[g]) { int u = pr.first; if (!inC[u] && !excl[u]) used[u >> 6] |= 1ULL << (u & 63); } }
        }
        if (m + lb > MAXS) return;
        int g = sc[0].second;
        vector<int> cand;
        for (auto& pr : grp[g]) if (!inC[pr.first] && !excl[pr.first]) cand.push_back(pr.first);
        vector<int> ex;
        for (int u : cand) {
            addu(u); dfs(); remu(u);
            if (found) return;
            excl[u] = 1; ex.push_back(u);
        }
        for (int u : ex) excl[u] = 0;
        return;
    }
    // closed
    if (good()) { found = true; best = C; return; }
    if (m >= MAXS) return;
    set<int> nb;
    for (int u : C) for (auto& pr : ug[u]) for (auto& q : grp[pr.first]) if (!inC[q.first] && !excl[q.first]) nb.insert(q.first);
    vector<int> ex;
    for (int u : nb) {
        addu(u); dfs(); remu(u);
        if (found) return;
        excl[u] = 1; ex.push_back(u);
    }
    for (int u : ex) excl[u] = 0;
}

int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r");
    MAXS = atoi(argv[2]);
    TL = argc > 3 ? atof(argv[3]) : 1e18;
    int MINS = argc > 4 ? atoi(argv[4]) : 1;
    int RF = argc > 5 ? atoi(argv[5]) : 0, RT = argc > 6 ? atoi(argv[6]) : 1000;
    if (fscanf(f, "%d %d %d", &n, &G, &nS) != 3) return 1;
    D.assign(n, vector<int>(nS));
    for (int u = 0; u < n; u++) for (int s = 0; s < nS; s++) if (fscanf(f, "%d", &D[u][s]) != 1) return 1;
    grp.resize(G); ug.resize(n);
    for (int g = 0; g < G; g++) {
        int sz; if (fscanf(f, "%d", &sz) != 1) return 1;
        for (int i = 0; i < sz; i++) { int u, l; if (fscanf(f, "%d %d", &u, &l) != 2) return 1; grp[g].push_back({u, l}); ug[u].push_back({g, l}); }
    }
    int np; if (fscanf(f, "%d", &np) != 1) return 1;
    perm.assign(np, vector<int>(n));
    for (int p = 0; p < np; p++) for (int u = 0; u < n; u++) if (fscanf(f, "%d", &perm[p][u]) != 1) return 1;
    fclose(f);
    W = (n + 63) / 64;
    inC.assign(n, 0); excl.assign(n, 0); cntg.assign(G, 0);
    // D-active orbit reps
    vector<int> orb(n, -1); vector<int> reps;
    for (int u = 0; u < n; u++) if (D[u][nS - 1] != 0 && orb[u] < 0) {
        int id = reps.size(); reps.push_back(u);
        for (int p = 0; p < np; p++) orb[perm[p][u]] = id;
    }
    printf("n %d groups %d D-active orbits %zu\n", n, G, reps.size()); fflush(stdout);
    T0 = chrono::steady_clock::now();
    int maxs = MAXS;
    try {
        for (int s = MINS; s <= maxs; s++) {
            MAXS = s; ll before = nodes;
            for (size_t i = RF; i < reps.size() && (int)i < RT && !found; i++) {
                // exclude D-active units of earlier orbits
                for (int u = 0; u < n; u++) excl[u] = (orb[u] >= 0 && orb[u] < (int)i) ? 1 : 0;
                addu(reps[i]); dfs(); remu(reps[i]);
            }
            double t = chrono::duration<double>(chrono::steady_clock::now() - T0).count();
            if (found) {
                printf("FOUND size %zu (max %d) nodes %lld t=%.1fs units:", best.size(), s, nodes, t);
                for (int u : best) printf(" %d", u);
                printf("\n");
                return 0;
            }
            printf("EXHAUSTED size <= %d : no good set; nodes %lld (this level %lld) t=%.1fs\n", s, nodes, nodes - before, t);
            fflush(stdout);
        }
    } catch (runtime_error&) {
        printf("TIMEOUT at size %d nodes %lld\n", MAXS, nodes);
    }
    return 0;
}
