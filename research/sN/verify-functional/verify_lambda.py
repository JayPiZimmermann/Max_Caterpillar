#!/usr/bin/env python3
"""Exact check of the analytic steps 1-4, 6 of the quadratic bound (NOTE.md).

For every locality L = (T, rho) and every key k of dictionary(N) (ALL keys of K0,
including auxiliary-looking ones) evaluate Lambda_L U_k exactly in Fractions:
  p_t = 0 (t in T), p_o = -B^rho(o);  eps = 1/(8C), delta = eps/2,
  q+- = p +- eps(e_a+e_b) with a<b the two smallest labels of T, d = e_a - e_b,
  J g(q) = g(q+delta d) + g(q-delta d) - 2 g(q), Lambda g = J g(q+) - J g(q-).
Parameters (MODE):
  'perkey' : B, C minimal stated values for that key alone:
             B = 2*max_o(|h_o|+N)+1,  C = 1 + max_{T} sum_{t in T}|h_t| + 2N
  'global' : B, C uniform over the whole dictionary (B from max over keys,
             C = 1 + max_k sum_all |h_t| + 2N).
Checks: (i) Lambda kills all aux functions; (ii) Lambda(max) = 2 delta;
(iii) Lambda U_k != 0 => Pass(k,L) [and the stronger A_k(p)=0 and M(T) != {}];
digit claim A_k(p)=0 <=> all c_o = 0; (iv) per-key counts.
Usage: python3 verify_lambda.py N [perkey|global]
"""
import itertools, math, sys
from fractions import Fraction as F
sys.path.insert(0, 'scripts')
from vocabulary_search import dictionary, aux_functions, eval_aux

N = int(sys.argv[1]); MODE = sys.argv[2] if len(sys.argv) > 2 else 'perkey'
relu = lambda t: t if t > 0 else 0
K0, _ = dictionary(N)
keys = sorted(K0, key=lambda k: (k[0], sorted(k[1])))

def A(k, y):
    h, M = k
    return sum(a * b for a, b in zip(h, y)) + sum(relu(y[i] - y[j]) for i, j in M)

def localities():
    for T in itertools.combinations(range(N), 3):
        out = [o for o in range(N) if o not in T]
        for perm in itertools.permutations(range(1, N - 2)):
            yield T, dict(zip(out, perm))

def stencil(T, rho, B, C):
    eps = F(1, 8 * C); dl = eps / 2
    p = [F(0) if o in T else F(-B ** rho[o]) for o in range(N)]
    a, b = T[0], T[1]
    pts = []
    for sgn, w0 in ((1, 1), (-1, -1)):          # q+, q- with weight +1, -1
        q = list(p); q[a] += sgn * eps; q[b] += sgn * eps
        for s, w in ((1, 1), (-1, 1), (0, -2)):
            z = list(q); z[a] += s * dl; z[b] -= s * dl
            pts.append((w0 * w, z))
    return p, pts, dl

def Lam(g, pts):
    return sum(w * g(z) for w, z in pts)

def Bk(k): return 2 * max(abs(x) + N for x in k[0]) + 1
def Ck(k): return 1 + max(sum(abs(k[0][t]) for t in T) for T in itertools.combinations(range(N), 3)) + 2 * N
Bg = max(Bk(k) for k in keys); Cg = 1 + max(sum(map(abs, k[0])) for k in keys) + 2 * N

def pass_pred(k, T, rho, p):
    h, M = k
    Ts = set(T)
    if A(k, p) != 0: return False
    MT = [e for e in M if e[0] in Ts and e[1] in Ts]
    if MT: return True
    v = {t: h[t] + sum(1 for i, j in M if i == t and j not in Ts) for t in T}
    nz = [x for x in v.values() if x]
    if not nz: return False
    if len(nz) == 2 and nz[0] == -nz[1]: return False
    return True

def digits(k, T, rho):
    h, M = k
    above = lambda u, o: (u in T) or (rho[u] < rho[o])
    c = {}
    for o in rho:
        kap = h[o] + sum(1 for i, j in M if i == o)
        nb = [j if i == o else i for i, j in M if o in (i, j)]
        c[o] = kap - sum(1 for u in nb if above(u, o))
    return c

aux = aux_functions(N)
# extra aux: all ordered differences (relu(x_j - x_i) too), constants, coordinates
extra = [('pair', j, i) for i in range(N) for j in range(N) if j > i]
stats = dict(aux_fail=0, max_fail=0, pass_fail=0, strong_fail=0, digit_fail=0,
             nonzero=0, pass_cnt=0, strong_cnt=0)
per_nz = {k: 0 for k in keys}; per_pass = {k: 0 for k in keys}; per_strong = {k: 0 for k in keys}; per_triples = {k: set() for k in keys}
nz_kinds = {}
nloc = 0
for T, rho in localities():
    nloc += 1
    if MODE.startswith('small'):   # deliberately undersized constants: diagnostic only
        Bs, Cs = map(int, MODE.split(':')[1:3])
        p, pts, dl = stencil(T, rho, Bs, Cs)
        for a_ in aux + extra:
            if Lam(lambda y: eval_aux(a_, y), pts) != 0: stats['aux_fail'] += 1
        if Lam(max, pts) != 2 * dl: stats['max_fail'] += 1
    if MODE == 'global':
        p, pts, dl = stencil(T, rho, Bg, Cg)
        for a_ in aux + extra:
            if Lam(lambda y: eval_aux(a_, y), pts) != 0: stats['aux_fail'] += 1
        if Lam(max, pts) != 2 * dl: stats['max_fail'] += 1
    for k in keys:
        if MODE == 'perkey':
            p, pts, dl = stencil(T, rho, Bk(k), Ck(k))
        val = Lam(lambda y: relu(A(k, y)), pts)
        Ap = A(k, p)
        c = digits(k, T, rho)
        if (Ap == 0) != all(x == 0 for x in c.values()): stats['digit_fail'] += 1
        pp = pass_pred(k, T, rho, p)
        if Ap == 0 and any(e[0] in T and e[1] in T for e in k[1]): stats['strong_cnt'] += 1; per_strong[k] += 1
        if pp: stats['pass_cnt'] += 1; per_pass[k] += 1
        if val != 0:
            stats['nonzero'] += 1; per_nz[k] += 1; per_triples[k].add(T)
            if not pp: stats['pass_fail'] += 1
            MT = [e for e in k[1] if e[0] in T and e[1] in T]
            if not (Ap == 0 and MT): stats['strong_fail'] += 1
            nz_kinds[val / dl] = nz_kinds.get(val / dl, 0) + 1
fN = math.factorial(N - 3)
mx = max(per_nz.values()); mxp = max(per_pass.values())
print(f'N={N} mode={MODE} keys={len(keys)} localities={nloc} (N!/6={math.factorial(N)//6})'
      f' Bg={Bg} Cg={Cg}')
print(' ', stats)
print(f'  max per key #(Lambda!=0) = {mx}, max per key #Pass = {mxp},'
      f' (N-2)(N-3)! = {(N-2)*fN}, 2(N-3)! = {2*fN}')
print('  max per key #(A=0 and M(T)!=empty) =', max(per_strong.values()))
print('  max #triples with Lambda!=0 per key =', max(len(s) for s in per_triples.values()))
print('  histogram of #(Lambda!=0) per key:', sorted(__import__('collections').Counter(per_nz.values()).items()))
print('  values Lambda/delta:', sorted(nz_kinds.items()))
print('  keys attaining max:', [ (k[0], sorted(k[1])) for k in keys if per_nz[k]==mx][:3])
