"""Tabulate graded S_N multiplicities of A_N and V_N (grade = |M|, grade -1 = A_N) from
cert_N.log (Young-subgroup ranks, Kostka inversion) and ysym2_N.log (Young symmetrizer).
Prints m_lam per grade increment, graded dims of V/A, and consistency between instruments."""
import json, sys
from kostka import partitions, conj, kostka, flam
def load(fn):
    out = []
    try:
        for l in open(fn):
            l = l.strip()
            if l.startswith('{'): out.append(json.loads(l))
    except FileNotFoundError: pass
    return out
def from_young(N, recs, key='rank_upper_prefix', need_cert=True):
    Ps = list(partitions(N))
    G = list(range(-1, N - 1))
    def pref(r):
        d = dict(zip(r['grades'], r[key])); v = []; last = 0
        for g in G: last = d.get(g, last); v.append(last)
        return v
    triv = {tuple(r['mu']): pref(r) for r in recs if r['twist'] == 'triv' and (r.get('certified', True) or not need_cert)}
    sgn = {tuple(r['mu']): pref(r) for r in recs if r['twist'] == 'sgn' and (r.get('certified', True) or not need_cert)}
    m = {}
    for lam in Ps:
        if lam in triv:
            m[lam] = [triv[lam][g] - sum(kostka(l, lam) * m[l][g] for l in m if l != lam) for g in range(len(G))]
    for mu in Ps:
        lam = conj(mu)
        if mu in sgn and lam not in m:
            m[lam] = [sgn[mu][g] - sum(kostka(conj(l), mu) * m[l][g] for l in m) for g in range(len(G))]
    return m
def from_ysym(N, recs):
    G = list(range(-1, N - 1)); m = {}
    for r in recs:
        d = dict(zip(r['grades'], r['mult_prefix'])); v = []; last = 0
        for g in G: last = d.get(g, last); v.append(last)
        m[tuple(r['lam'])] = v
    return m
def show(N, m, name):
    Ps = list(partitions(N)); G = list(range(-1, N - 1))
    print(f'== N={N} source={name}  (prefix multiplicities, grades {G})')
    for lam in Ps:
        if lam in m: print('  ', ''.join(map(str, lam)), 'f=', flam(lam), m[lam])
    if all(l in m for l in Ps):
        dims = [sum(flam(l) * m[l][g] for l in Ps) for g in range(len(G))]
        inc = [dims[0]] + [dims[g] - dims[g - 1] for g in range(1, len(G))]
        print('   dim prefix', dims, ' increments (A, |M|=0,1,..)', inc, ' q=', dims[-1] - dims[0])
        # quotient multiplicities
        print('   V/A multiplicities:', {''.join(map(str, l)): m[l][-1] - m[l][0] for l in Ps})
        for g in range(1, len(G)):
            print(f'   grade |M|={G[g]} mults:', {''.join(map(str, l)): m[l][g] - m[l][g - 1] for l in Ps if m[l][g] - m[l][g - 1]})
for N in (3, 4, 5, 6):
    c = load(f'cert_{N}.log') + load(f'cert_{N}_321sgn.log')
    if c: show(N, from_young(N, c), 'certified Young-subgroup ranks')
    g = load(f'grade_{N}.log')
    if g: show(N, from_young(N, [dict(r, rank_upper_prefix=r['ranks_A_then_by_M'], grades=list(range(-1, len(r['ncols']) - 1))) for r in g]), 'measured grade.py')
    y = load(f'ysym2_{N}.log') or load(f'ysym_{N}.log')
    if y: show(N, from_ysym(N, y), 'measured Young symmetrizer')
