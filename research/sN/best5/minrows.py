"""EXACT: smallest first layer (model B) that carries the second-layer inputs of a given
identity max_5 = sum_k d_k relu(t_k) (targets t_k = <lam_k,x> + sum b_ij |x_i - x_j|).
Rows: oriented pair hinges relu(+-(x_i-x_j)) and +-pairs relu(v.x), relu(-v.x) (giving the linear form v).
A pair used by some target needs >= 1 orientation; one orientation s fixes the row coefficient 2b and
adds linear part b*s*(e_i-e_j); both orientations make e_i-e_j free.  Remaining linear parts must lie in
span(free differences) + V, V spanned by +-pairs (2 rows per dimension).
Usage: python minrows.py   (targets: the h2=6 model-A network netA_h2_6 rewritten as targets)"""
import itertools, runpy, os, sympy
from fractions import Fraction as Fr
N = 5

def targets_from_spec():
    spec = runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../dfs/h4-general-neurons/r2_spec_N5_k4.py'))
    out = []
    def conv(l, a, sgn=1):
        lam = [Fr(sgn) * Fr(c) for c in l]; b = {}
        for (i, j), c in a.items():
            c = Fr(sgn) * Fr(c)
            lam[i] += c / 2; lam[j] -= c / 2; b[(i, j)] = b.get((i, j), 0) + c / 2
        return lam, {p: v for p, v in b.items() if v}
    l, a = spec['R']
    out.append(conv(l, a)); out.append(conv(l, a, -1))
    for d, l, a in spec['NEURONS']:
        out.append(conv(l, a))
    return out

def rank(vecs):
    if not vecs: return 0
    return sympy.Matrix(vecs).rank()

def best(T):
    pairs = sorted({p for _, b in T for p in b})
    res = []
    for ori in itertools.product(('+', '-', '2'), repeat=len(pairs)):
        D = []
        r = []
        for (lam, b) in T:
            v = list(lam)
            for p, o in zip(pairs, ori):
                if o != '2' and p in b:
                    s = 1 if o == '+' else -1
                    v[p[0]] -= b[p] * s; v[p[1]] += b[p] * s
            r.append(v)
        for p, o in zip(pairs, ori):
            if o == '2':
                e = [0] * N; e[p[0]] = 1; e[p[1]] = -1; D.append(e)
        dimV = rank(D + [x for x in r if any(x)]) - rank(D)
        h1 = len(pairs) + len(D) + 2 * dimV
        res.append((h1, dimV, dict(zip(pairs, ori))))
    res.sort(key=lambda t: t[0])
    return res

if __name__ == '__main__':
    T = targets_from_spec()
    for lam, b in T:
        print('target lam', [str(c) for c in lam], 'b', {p: str(v) for p, v in b.items()})
    R = best(T)
    m = R[0][0]
    print('minimum h1 =', m)
    for r in R:
        if r[0] == m: print('  ', r)
