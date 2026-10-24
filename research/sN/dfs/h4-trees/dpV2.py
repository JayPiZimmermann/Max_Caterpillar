#!/usr/bin/env python3
"""Tree DP for the local relaxation V2 (branch h4-trees).
Child summary (sigma, gamma, omega, alpha):
  sigma = s (child in S, not needing parent in S),
  gamma = c0/2 + c1 (child O, component closed),
  omega = o0 + o1 (child O, component open: needs parent in O below it),
  alpha = s + s* + x (c0 + c1)  (total when the parent is in S).
Final F = s/x + c0 + c1 at the global root.  Cross-checked against relaxV2.py."""
import itertools, sys, random
from fractions import Fraction
x = Fraction(1, 2)

def node(e, kids):
    """kids: list of child state dicts.  Returns state dict of this vertex."""
    st = {}
    pa = Fraction(1)
    for k in kids: pa *= k['alpha']
    if not kids and e == 0:
        st['s'] = Fraction(0); st['sstar'] = x
    else:
        st['s'] = x ** (1 + e) * pa; st['sstar'] = Fraction(0)
    sig = [k['s'] for k in kids]; so = [k['s'] + k['omega'] for k in kids]; gam = [k['gamma'] for k in kids]
    P = lambda L: eval('*'.join(['1'] + ['L[%d]' % i for i in range(len(L))])) if L else 1
    def prod(L):
        r = Fraction(1)
        for t in L: r *= t
        return r
    c0 = c1 = o0 = o1 = Fraction(0)
    if e == 1:
        c0 = prod(sig); c1 = (prod(so) - prod(sig)) / 2
    elif e == 0:
        o0 = prod(sig); o1 = (prod(so) - prod(sig)) / 2
        for kk in range(len(kids)):
            rs = [sig[j] for j in range(len(kids)) if j != kk]
            rso = [so[j] for j in range(len(kids)) if j != kk]
            c0 += gam[kk] * prod(rs); c1 += gam[kk] * (prod(rso) - prod(rs)) / 2
    st.update(c0=c0, c1=c1, o0=o0, o1=o1)
    st['gamma'] = c0 / 2 + c1; st['omega'] = o0 + o1
    st['alpha'] = st['s'] + st['sstar'] + x * (c0 + c1)
    return st

def final(st):
    return st['s'] / x + st['c0'] + st['c1']

def eval_tree(adj, e, root):
    def rec(v, p):
        return node(e[v], [rec(w, v) for w in adj[v] if w != p])
    return rec(root, None)

if __name__ == '__main__':
    from classW_fast import free_trees
    n = int(sys.argv[1]); emax = int(sys.argv[2])
    worst = Fraction(0); pts = []
    for edges in (free_trees(list(range(n))) if n > 1 else [[]]):
        adj = {v: [] for v in range(n)}
        for u, w in edges: adj[u].append(w); adj[w].append(u)
        for e in itertools.product(range(emax + 1), repeat=n):
            root = max(range(n), key=lambda v: len(adj[v]))
            F = final(eval_tree(adj, e, root))
            if F > worst: worst = F
    print(f'n={n}: max F (DP) = {worst}')
