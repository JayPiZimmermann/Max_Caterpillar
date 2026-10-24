"""EXACT certificate: a zero-bias two-hidden-layer ReLU network equals max(x_0..x_{N-1}) on R^N.

Network JSON: {"N":N, "first_layer":[[a_j0..a_j,N-1] ...]  (h1 rows),
               "second_layer":[[W_k0..W_k,h1-1] ...] (h2 rows), "output":[d_0..d_{h2-1}]}
numbers are ints or strings "p/q".  F(x) = sum_k d_k relu(sum_j W_kj relu(a_j . x)).

Method (pure Fraction arithmetic, independent of any fitting code):
depth-first refinement of R^N by (1) a braid cell x_pi0 > ... > x_pi(N-1),
(2) the sign of every first-layer form a_j.x, (3) the sign of every second-layer
preactivation, which is a linear form on the region fixed by (1)-(2).
Each branch is kept only if the open homogeneous cone {r.x > 0 : r in constraints}
is nonempty, decided EXACTLY: a rational interior witness (checked by exact
substitution) proves nonemptiness; otherwise exact Fourier-Motzkin elimination
decides.  Forms identically zero on a region are not branched on.
At every leaf (a nonempty open cone) F is the linear form
sum_{k active} d_k W_k . (a_j active rows) and must equal x_pi0 coefficientwise.
The leaves are disjoint open cones whose union is dense in R^N (the complement lies
in finitely many hyperplanes); F - max is continuous, so it vanishes on R^N.
Usage: python cert.py net.json  -> prints counts and PASS/FAIL (exit code 0 iff PASS)."""
import sys, json, itertools
from fractions import Fraction as Fr


def fr(v):
    return Fr(v) if not isinstance(v, str) else Fr(v)


def normalize(r):
    g = next((abs(c) for c in r if c != 0), None)
    return tuple(c / g for c in r) if g else tuple(r)


def fm_feasible(rows):
    rows = [list(r) for r in rows]
    n = len(rows[0])
    for var in range(n):
        if any(all(c == 0 for c in r) for r in rows):
            return False
        pos = [r for r in rows if r[var] > 0]
        neg = [r for r in rows if r[var] < 0]
        new = [r for r in rows if r[var] == 0]
        for p in pos:
            for q in neg:
                new.append([p[t] * (-q[var]) + q[t] * p[var] for t in range(n)])
        seen, rows = set(), []
        for r in new:
            k = normalize(r)
            if k not in seen:
                seen.add(k); rows.append(list(k))
        if not rows:
            return True
    return not any(all(c == 0 for c in r) for r in rows)


class Feas:
    def __init__(self, N):
        self.N = N
        self.cache = {}
        self.stats = [0, 0]

    def __call__(self, rows, hint=None):
        key = frozenset(normalize(r) for r in rows)
        if key in self.cache:
            return self.cache[key]
        ok = None
        if hint is not None and all(sum(c * x for c, x in zip(r, hint)) > 0 for r in rows):
            ok = True; self.stats[0] += 1
        if ok is None:
            ok = fm_feasible(rows); self.stats[1] += 1
        self.cache[key] = ok
        return ok


def certify(net, verbose=True):
    N = net['N']
    A = [[fr(c) for c in row] for row in net['first_layer']]
    W = [[fr(c) for c in row] for row in net['second_layer']]
    d = [fr(c) for c in net['output']]
    h1, h2 = len(A), len(W)
    assert all(len(r) == N for r in A) and all(len(r) == h1 for r in W) and len(d) == h2
    feas = Feas(N)
    leaves, fails = 0, []

    def dot(r, x):
        return sum(c * v for c, v in zip(r, x))

    for perm in itertools.permutations(range(N)):
        cell = []
        for t in range(N - 1):
            r = [Fr(0)] * N; r[perm[t]] += 1; r[perm[t + 1]] -= 1; cell.append(r)
        # interior hint point of the cell
        hint = [Fr(0)] * N
        for t, i in enumerate(perm):
            hint[i] = Fr(N - t)

        def rec1(j, cons, act):
            if j == h1:
                # first-layer outputs are linear forms: row j active -> A[j], else 0
                pre = []
                for k in range(h2):
                    v = [Fr(0)] * N
                    for jj in range(h1):
                        if act[jj] and W[k][jj] != 0:
                            for t in range(N):
                                v[t] += W[k][jj] * A[jj][t]
                    pre.append(v)
                rec2(0, cons, pre, [Fr(0)] * N)
                return
            v = A[j]
            if not any(v):
                rec1(j + 1, cons, act + [False]); return
            for s in (1, -1):
                c2 = cons + [[s * c for c in v]]
                if feas(c2, None):
                    rec1(j + 1, c2, act + [s == 1])

        def rec2(k, cons, pre, form):
            nonlocal leaves
            if k == h2:
                leaves += 1
                diff = list(form); diff[perm[0]] -= 1
                if any(diff):
                    fails.append((perm, cons, form))
                return
            v = pre[k]
            if d[k] == 0 or not any(v):
                rec2(k + 1, cons, pre, form); return
            for s in (1, -1):
                c2 = cons + [[s * c for c in v]]
                if feas(c2, None):
                    f2 = [form[t] + d[k] * v[t] for t in range(N)] if s == 1 else form
                    rec2(k + 1, c2, pre, f2)

        rec1(0, cell, [])
    ok = not fails
    if verbose:
        print('N %d h1 %d h2 %d: braid cells %d, leaf regions %d, FM calls %d, failures %d -> %s'
              % (N, h1, h2, len(list(itertools.permutations(range(N)))), leaves, feas.stats[1],
                 len(fails), 'PASS' if ok else 'FAIL'))
        for p, c, f in fails[:3]:
            print('  FAIL perm', p, 'form', [str(x) for x in f])
    return ok


if __name__ == '__main__':
    net = json.load(open(sys.argv[1]))
    sys.exit(0 if certify(net) else 1)
