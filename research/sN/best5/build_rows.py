"""Build an exact model-(B) network from targets (minrows.py) and a hinge-orientation choice:
rows = chosen oriented hinges, then +-v for a rational basis v of the needed extra linear space V.
Second-layer row of target t solves t = sum_rows w_r relu(r.x) exactly.
Usage: python build_rows.py out.json '<orientation dict>'"""
import sys, json, ast, sympy
from fractions import Fraction as Fr
from minrows import targets_from_spec, N
from phiA import net_json

def build(T, ori):
    rows = []      # (vector, kind)
    idx = {}
    for p, o in sorted(ori.items()):
        e = [0] * N; e[p[0]] = 1; e[p[1]] = -1
        if o in ('+', '2'):
            idx[(p, 1)] = len(rows); rows.append(e)
        if o in ('-', '2'):
            idx[(p, -1)] = len(rows); rows.append([-c for c in e])
    D = [[1 if t == p[0] else -1 if t == p[1] else 0 for t in range(N)] for p, o in ori.items() if o == '2']
    resid = []
    for lam, b in T:
        v = list(lam)
        for p, c in b.items():
            o = ori[p]
            if o != '2':
                s = 1 if o == '+' else -1
                v[p[0]] -= c * s; v[p[1]] += c * s
        resid.append(v)
    # basis of V: residuals not in span(D), greedy
    Vb = []
    for v in resid:
        M0 = sympy.Matrix(D + Vb) if D + Vb else None
        r0 = M0.rank() if M0 is not None else 0
        if sympy.Matrix(D + Vb + [v]).rank() > r0:
            Vb.append(v)
    for v in Vb:
        rows.append(list(v)); rows.append([-c for c in v])
    # solve each target: functions relu(r.x); use exact decomposition into |.| and linear parts
    W = []
    for (lam, b), v in zip(T, resid):
        w = [Fr(0)] * len(rows)
        lin = [Fr(c) for c in lam]
        for p, c in b.items():
            o = ori[p]
            if o == '2':  # use + orientation with coefficient 2c: gives c|.| + c(e_i-e_j)
                w[idx[(p, 1)]] += 2 * c; lin[p[0]] -= c; lin[p[1]] += c
            else:
                s = 1 if o == '+' else -1
                w[idx[(p, s)]] += 2 * c; lin[p[0]] -= c * s; lin[p[1]] += c * s
        # lin = remaining linear part; write as combination of free differences (D, via both orientations) and V
        basis = D + Vb
        if any(lin):
            M = sympy.Matrix(basis).T
            sol = M.solve_least_squares(sympy.Matrix([sympy.Rational(c.numerator, c.denominator) for c in lin]))
            assert M * sol == sympy.Matrix([sympy.Rational(c.numerator, c.denominator) for c in lin])
            k = 0
            for p, o in ori.items():
                if o == '2':
                    c = Fr(str(sol[k])); k += 1
                    w[idx[(p, 1)]] += c; w[idx[(p, -1)]] -= c
            for j, vv in enumerate(Vb):
                c = Fr(str(sol[k])); k += 1
                base = len(rows) - 2 * len(Vb) + 2 * j
                w[base] += c; w[base + 1] -= c
        W.append(w)
    return rows, W

if __name__ == '__main__':
    import runpy, os
    T = targets_from_spec()
    ori = ast.literal_eval(sys.argv[2])
    rows, W = build(T, ori)
    spec = runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../dfs/h4-general-neurons/r2_spec_N5_k4.py'))
    d = [Fr(1), Fr(-1)] + [Fr(n[0]) for n in spec['NEURONS']]
    json.dump(net_json(N, rows, W, d), open(sys.argv[1], 'w'), indent=1)
    print('h1', len(rows), 'h2', len(W))
