#!/usr/bin/env python3
"""Per-component partition functions for the exponential bound (main-session branch).

For a unit (caterpillar tree with edge states), F = hinge forest, kappa as in
NOTE.md. The weight of k-localities factorizes over components C of F:
  W_k = [x^k] prod_C G_C(x),  G_C(x) = sum_{S subset C} [s_C(S)] q_C(S) x^|S|,
where q_C(S) = probability that a uniformly random order of C \\ S gives every
vertex o of C \\ S exactly kappa_o neighbours above it (S counts as above), and
s_C(S): every t in S has v_t != 0 or a hinge-neighbour in S, with
v_t = kappa_t - #{hinge neighbours of t in S with larger index} (key level;
on the tree we use the equivalent tree formula below).
Reports: max over components with |C| >= 2 of q_C(empty) (should be <= 1/2) and
of Z_C = sum_{S nonempty} [s] q_C(S); and checks W_k <= [x^k]-bound.
"""
import itertools, math, sys
from fractions import Fraction
N = int(sys.argv[1]); r = N - 2


def caterpillar(S):
    edges = []
    for j in range(1, r + 1):
        p = max([0] + [i for i in S if i < j])
        edges.append((p + 1, j + 1))
    return edges, max(S) + 1


def q(C, S, nbr, mu):
    rest = [o for o in C if o not in S]
    if any(mu[o] < 0 or mu[o] > len(nbr[o]) for o in rest): return Fraction(0)
    idx = {o: i for i, o in enumerate(rest)}
    count = {0: 1}
    for _ in range(len(rest)):
        new = {}
        for placed, cnt in count.items():
            for o in rest:
                b = 1 << idx[o]
                if placed & b: continue
                below = sum(1 for u in nbr[o] if u not in S and not placed & (1 << idx[u]))
                if below == mu[o]: new[placed | b] = new.get(placed | b, 0) + cnt
        count = new
    return Fraction(sum(count.values()), math.factorial(len(rest)))


maxq0 = Fraction(0); maxZ = Fraction(0); argZ = None
XS=[Fraction(1,2),Fraction(1,3),Fraction(1,4),Fraction(1,5),Fraction(1,6),Fraction(1,8)]
maxG={x:Fraction(0) for x in XS}; argG={}
for size in range(1, r + 1):
    for Scut in itertools.combinations(range(1, r + 1), size):
        edges, last = caterpillar(Scut)
        for states in itertools.product(range(3), repeat=r):
            mu = [0] * N; nbr = [[] for _ in range(N)]
            mu[0] += 1; mu[last] -= 1
            lin = []
            for (p, c), s in zip(edges, states):
                if s: mu[c] += 1
                if s == 1: mu[p] -= 1; lin.append((p, c))
                if s == 2: nbr[p].append(c); nbr[c].append(p)
            # components of F
            seen = set(); comps = []
            for v in range(N):
                if v in seen: continue
                stack = [v]; comp = []
                seen.add(v)
                while stack:
                    x = stack.pop(); comp.append(x)
                    for y in nbr[x]:
                        if y not in seen: seen.add(y); stack.append(y)
                comps.append(sorted(comp))
            for C in comps:
                if len(C) < 2: continue
                q0 = q(C, set(), nbr, mu)
                maxq0 = max(maxq0, q0)
                Z = Fraction(0); poly={}
                for m in range(1, len(C) + 1):
                    for S in itertools.combinations(C, m):
                        Ss = set(S)
                        # s_C(S) on the tree: v_t = T-part of outer slope (head, linear, active hinges)
                        ok = True
                        for t in S:
                            vt = (1 if t == last else 0) - (1 if t == 0 else 0)
                            for (p, c) in lin:
                                if p == t: vt += 1
                                if c == t: vt -= 1
                            hinS = False
                            for (p, c), s in zip(edges, states):
                                if s == 2 and t in (p, c):
                                    other = c if p == t else p
                                    if other in Ss: hinS = True
                                    elif p == t: vt += 1
                            if vt == 0 and not hinS: ok = False; break
                        if ok:
                            qq=q(C, Ss, nbr, mu); Z += qq; poly[m]=poly.get(m,0)+qq
                if Z > maxZ: maxZ, argZ = Z, (Scut, states, C)
                for x in XS:
                    G=q0+sum(c*x**m for m,c in poly.items())
                    if G>maxG[x]: maxG[x]=G; argG[x]=(Scut,states,C,dict(poly),q0)
print('N',N,{str(x):float(g) for x,g in maxG.items()}); print(' arg x=1/4:',argG[Fraction(1,4)])
print(f'N={N}: max q_C(empty) over |C|>=2: {maxq0}; max Z_C: {maxZ} = {float(maxZ):.4f} at {argZ}', flush=True)
