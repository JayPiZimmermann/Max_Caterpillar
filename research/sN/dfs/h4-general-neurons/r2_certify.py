"""EXACT certificate for an identity
    max_N(x) = R(x) + sum_k d_k relu(g_k(x))   on all of R^N,
g_k(x) = <l_k, x> + sum_{i<j} a^k_ij relu(x_i - x_j),  R of the same form (rational data).

Method (all arithmetic in Fractions):
On the open braid cell C_pi = {x_pi(0) > ... > x_pi(N-1)} every g_k is a linear
form L_k. For every sign vector s in {+,-}^K (over neurons whose L_k is not identically
zero on C_pi) we decide exactly, by Fourier-Motzkin elimination for the homogeneous
STRICT system {cell inequalities, s_k L_k > 0}, whether the open cone
C_pi(s) is nonempty. On a nonempty C_pi(s) the difference
D = R + sum d_k relu(g_k) - max_N is the linear form
R|C + sum_{s_k=+} d_k L_k - x_pi(0); we require it to be the zero form.
The cones C_pi(s) (s realizable) cover a dense open subset of R^N, D is continuous,
hence D == 0 on R^N.  Output: number of cells, realizable regions, failures.
Usage: python r2_certify.py <spec.py>   (spec defines N, R=(l,a), NEURONS=[(d,l,a)])
"""
import itertools, sys, runpy
from fractions import Fraction as Fr


def pairs(N):
    return list(itertools.combinations(range(N), 2))


def lin_on_cell(N, l, a, rank):
    """linear form of <l,x> + sum a_ij relu(x_i-x_j) on the cell; rank[i] = position (0 = largest)."""
    v = [Fr(t) for t in l]
    for (i, j), c in a.items():
        if c and rank[i] < rank[j]:  # x_i > x_j
            v[i] += c
            v[j] -= c
    return v


def feasible_strict(rows):
    """Is {x : r . x > 0 for all r in rows} nonempty? Exact Fourier-Motzkin."""
    rows = [list(r) for r in rows]
    if not rows:
        return True
    n = len(rows[0])
    for var in range(n):
        if any(all(c == 0 for c in r) for r in rows):
            return False
        pos = [r for r in rows if r[var] > 0]
        neg = [r for r in rows if r[var] < 0]
        zer = [r for r in rows if r[var] == 0]
        new = zer[:]
        for p in pos:
            for q in neg:
                new.append([p[t] * (-q[var]) + q[t] * p[var] for t in range(n)])
        # remove duplicates / positive multiples
        seen, rows = set(), []
        for r in new:
            g = next((abs(c) for c in r if c != 0), None)
            key = tuple(c / g for c in r) if g else tuple(r)
            if key not in seen:
                seen.add(key)
                rows.append(list(key))
        if not rows:
            return True
    return not any(all(c == 0 for c in r) for r in rows)


def certify(N, R, NEURONS, verbose=True):
    nreg, fails = 0, []
    for perm in itertools.permutations(range(N)):
        rank = {perm[t]: t for t in range(N)}
        cell = []
        for t in range(N - 1):
            r = [Fr(0)] * N
            r[perm[t]] += 1
            r[perm[t + 1]] -= 1
            cell.append(r)
        base = lin_on_cell(N, R[0], R[1], rank)
        base[perm[0]] -= 1
        L = [(Fr(d), lin_on_cell(N, l, a, rank)) for d, l, a in NEURONS]
        L = [(d, v) for d, v in L if d != 0 and any(v)]
        # DFS over sign vectors with pruning on infeasible prefixes
        def rec(k, cons, form):
            nonlocal nreg
            if not feasible_strict(cons):
                return
            if k == len(L):
                nreg += 1
                if any(form):
                    fails.append((perm, form))
                return
            d, v = L[k]
            rec(k + 1, cons + [v], [form[t] + d * v[t] for t in range(N)])
            rec(k + 1, cons + [[-c for c in v]], form)
        rec(0, cell, base)
    if verbose:
        print('N', N, 'cells', len(list(itertools.permutations(range(N)))), 'realizable regions', nreg,
              'failures', len(fails))
        for f in fails[:5]:
            print('  FAIL', f)
    return nreg, fails


if __name__ == '__main__':
    spec = runpy.run_path(sys.argv[1])
    certify(spec['N'], spec['R'], spec['NEURONS'])
