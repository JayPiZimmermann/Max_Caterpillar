#!/usr/bin/env python3
"""Check the hook/heap reformulation and the local relaxation (branch h4-trees).

Tree C, e_o = kappa_o - deg(o) + 1 >= 0 (property P1).  Claim A (exact):
  G_C(x) = sum_{S,(s)} x^|S| prod_{K comp of C-S} [K has one e=1 vertex z, others e=0] / hook(K rooted at z).
Claim B (relaxed, local): with hook replaced by prod_{v in O} (deg_O(v) + e_v),
  R(C) = sum_S x^{|S| + sum_S e + c(S) - 1} prod_{v in O} 1/(deg_O(v)+e_v) <= 1  at x = 1/2.
Usage: python relaxP1.py n emax"""
import sys, itertools
from fractions import Fraction
from classW_fast import free_trees
import wcount as wc
if __name__ != "__main__": raise ImportError
n = int(sys.argv[1]); emax = int(sys.argv[2]); x = Fraction(1, 2)

def comps(vs, adj):
    vs = set(vs); out = []
    while vs:
        s = vs.pop(); st = [s]; K = {s}
        while st:
            u = st.pop()
            for w in adj[u]:
                if w in vs: vs.remove(w); K.add(w); st.append(w)
        out.append(K)
    return out

def hook(K, z, adj):
    # product of subtree sizes rooted at z
    prod = 1
    def size(u, p):
        nonlocal prod
        s = 1
        for w in adj[u]:
            if w in K and w != p: s += size(w, u)
        prod *= s
        return s
    size(z, None)
    return prod

worstB = Fraction(0); argB = None; maxA_err = 0; worstA = Fraction(0)
for edges in (free_trees(list(range(n))) if n > 1 else [[]]):
    adj = {v: [] for v in range(n)}
    for u, w in edges: adj[u].append(w); adj[w].append(u)
    deg = [len(adj[v]) for v in range(n)]
    for e in itertools.product(range(emax + 1), repeat=n):
        kap = [deg[v] - 1 + e[v] for v in range(n)]
        GA = Fraction(0); R = Fraction(0)
        for mask in range(1 << n):
            S = {v for v in range(n) if mask >> v & 1}
            if any(not (set(adj[t]) & S) and kap[t] == 0 for t in S): continue
            O = [v for v in range(n) if v not in S]
            Ks = comps(O, adj)
            ok = True; qa = Fraction(1); qb = Fraction(1)
            for K in Ks:
                ones = [v for v in K if e[v] == 1]
                if len(ones) != 1 or any(e[v] > 1 for v in K): ok = False; break
                qa /= hook(K, ones[0], adj)
            if not ok: continue
            for v in O:
                dO = sum(1 for w in adj[v] if w not in S)
                qb /= (dO + e[v])
            GA += x ** len(S) * qa
            R += x ** (len(S) + sum(e[v] for v in S) + len(Ks) - 1) * qb
        # compare A with direct counter
        nbr = [sum(1 << w for w in adj[v]) for v in range(n)]
        w = wc.weights(n, nbr, kap)
        Gd = sum(w[s] * x ** s for s in range(n + 1))
        if Gd != GA: maxA_err += 1
        D = sum(kap) - (n - 1)
        worstA = max(worstA, GA * x ** D)
        if R > worstB: worstB = R; argB = (edges, e)
print(f'n={n} emax={emax}: claim A mismatches {maxA_err}; max G x^D = {worstA}; max relaxed R = {worstB} = {float(worstB):.4f} at {argB}')
