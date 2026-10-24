"""MILP search (HiGHS) for free-remainder identities  max_5 = R + sum_{k<K} d_k relu(g_k)
(g_k translation-invariant pair functions, R pair function, d_k = +-1), in RAY / SET-FUNCTION form:
  v_k(S) = g_k(1_S)  (S nonempty proper subset of [5]),  u_k = relu(v_k),  f = sum d_k u_k.
max_5 - F lies in span{x_i, relu(x_i-x_j)}  <=>  F is linear on every braid cell  and  the Moebius
coefficients of f of order >= 3 equal those of max_5, i.e. (-1)^(|S|+1).
Braid linearity is imposed per maximal chain (= braid cell): each neuron either has weakly constant
sign on the chain, or is cancelled by a partner j with d_j = -d_k and v_j = +-v_k on the chain
(pair cancellation; triple cancellations are not searched).  Big-M bound |v| <= B.
A solution is a candidate only; it is rationalized and certified exactly (cert.py) afterwards.
Usage: python milp_k.py K dsigns B timelimit_s [out.npz]     e.g. python milp_k.py 3 ++- 8 3000"""
import sys, itertools, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

N = 5
PAIRS = list(itertools.combinations(range(N), 2))
SETS = [frozenset(c) for r in range(1, N) for c in itertools.combinations(range(N), r)]
SID = {S: i for i, S in enumerate(SETS)}
CHAINS = [[frozenset(p[:t + 1]) for t in range(N - 1)] for p in itertools.permutations(range(N))]


def vrow(S):
    """coefficients of v(S) in terms of (l_0..l_4, a_pairs): v(S) = sum_{i in S} l_i + sum_{i in S, j not in S} relu-hinge
    relu(x_i - x_j) at 1_S equals 1 iff i in S and j not in S (pairs i<j), for orientation i<j."""
    r = np.zeros(N + len(PAIRS))
    for i in S:
        r[i] = 1
    for q, (i, j) in enumerate(PAIRS):
        if i in S and j not in S:
            r[N + q] = 1
    return r


def build(K, d, B):
    nP = N + len(PAIRS)                       # 15 params per neuron
    nS = len(SETS)                            # 30
    opp = [(i, j) for i, j in itertools.combinations(range(K), 2) if d[i] != d[j]]
    nC = len(CHAINS)
    # variable layout
    off = {}
    n = 0
    def alloc(name, size):
        nonlocal n
        off[name] = n; n += size
    alloc('p', K * nP); alloc('u', K * nS); alloc('z', K * nS)
    alloc('yp', K * nC); alloc('ym', K * nC)
    alloc('e', len(opp) * nC * 2)
    integ = np.zeros(n); integ[off['z']:] = 1
    lb = np.full(n, -np.inf); ub = np.full(n, np.inf)
    lb[off['u']:off['u'] + K * nS] = 0
    lb[off['z']:] = 0; ub[off['z']:] = 1
    rows, lo, hi = [], [], []
    def add(coefs, l, h):
        rows.append(coefs); lo.append(l); hi.append(h)
    VR = {S: vrow(S) for S in SETS}
    def vcoef(k, S, scale=1.0):
        return {off['p'] + k * nP + t: scale * c for t, c in enumerate(VR[S]) if c}
    def merge(*ds):
        out = {}
        for dd in ds:
            for kk, vv in dd.items():
                out[kk] = out.get(kk, 0) + vv
        return out
    for k in range(K):
        add({off['p'] + k * nP + t: 1 for t in range(N)}, 0, 0)       # translation invariance
        for S in SETS:
            u = off['u'] + k * nS + SID[S]; z = off['z'] + k * nS + SID[S]
            add(merge(vcoef(k, S), {}), -B, B)                          # |v| <= B
            add(merge({u: 1}, vcoef(k, S, -1)), 0, np.inf)              # u >= v
            add(merge({u: 1, z: B}, vcoef(k, S, -1)), -np.inf, B)       # u <= v + B(1-z)
            add({u: 1, z: -B}, -np.inf, 0)                              # u <= B z
    # Moebius equations, |S| >= 3 (including S = [5] where u = 0)
    allS = [frozenset(c) for r in range(3, N + 1) for c in itertools.combinations(range(N), r)]
    for S in allS:
        co = {}
        for r in range(1, len(S) + 1):
            for U in itertools.combinations(sorted(S), r):
                U = frozenset(U)
                if len(U) == N:
                    continue
                sg = (-1) ** (len(S) - len(U))
                for k in range(K):
                    key = off['u'] + k * nS + SID[U]
                    co[key] = co.get(key, 0) + d[k] * sg
        rhs = (-1) ** (len(S) + 1)
        add(co, rhs, rhs)
    # chain constraints
    for c, ch in enumerate(CHAINS):
        for k in range(K):
            yp = off['yp'] + k * nC + c; ym = off['ym'] + k * nC + c
            cov = {yp: 1, ym: 1}
            for q, (i, j) in enumerate(opp):
                if k in (i, j):
                    for s in range(2):
                        cov[off['e'] + (q * nC + c) * 2 + s] = 1
            add(cov, 1, np.inf)
            for S in ch:
                add(merge(vcoef(k, S), {yp: -B}), -B, np.inf)           # v >= -B(1-yp)
                add(merge(vcoef(k, S), {ym: B}), -np.inf, B)            # v <= B(1-ym)
        for q, (i, j) in enumerate(opp):
            for s, sg in enumerate((1, -1)):
                e = off['e'] + (q * nC + c) * 2 + s
                for S in ch:
                    diff = merge(vcoef(j, S), vcoef(i, S, -sg))
                    add(merge(diff, {e: 2 * B}), -np.inf, 2 * B)
                    add(merge(diff, {e: -2 * B}), -2 * B, np.inf)
    A = lil_matrix((len(rows), n))
    for r, co in enumerate(rows):
        for kk, vv in co.items():
            A[r, kk] = vv
    return A.tocsr(), np.array(lo), np.array(hi), integ, lb, ub, off, nP


if __name__ == '__main__':
    K = int(sys.argv[1]); d = [1 if ch == '+' else -1 for ch in sys.argv[2]]
    B = float(sys.argv[3]); tl = float(sys.argv[4])
    out = sys.argv[5] if len(sys.argv) > 5 else 'milp_K%d_%s.npz' % (K, sys.argv[2].replace('+', 'p').replace('-', 'm'))
    t0 = time.time()
    A, lo, hi, integ, lb, ub, off, nP = build(K, d, B)
    print('K', K, 'd', d, 'B', B, 'vars', A.shape[1], 'cons', A.shape[0], 'binaries', int(integ.sum()), flush=True)
    rng = np.random.default_rng(0)
    res = milp(c=np.zeros(A.shape[1]), constraints=LinearConstraint(A, lo, hi), integrality=integ,
               bounds=Bounds(lb, ub), options={'time_limit': tl, 'disp': False})
    print('status', res.status, res.message, '%.0fs' % (time.time() - t0), flush=True)
    if res.x is not None:
        P = res.x[:K * nP].reshape(K, nP)
        np.savez(out, P=P, d=np.array(d), B=B)
        np.set_printoptions(precision=4, suppress=True, linewidth=200)
        print(P)
