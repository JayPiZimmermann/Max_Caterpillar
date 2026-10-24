#!/usr/bin/env python3
"""Exact check of an explicit m = 4 twin-killing functional (unit-cube form).
Phi f = sum_{y} W(y) U_y f, U_y f = sum_{S} (-1)^{4-|S|} f(y + 1_S), W = 1 on the S_4-orbits of
(0,0,0,0), (0,0,2,2), (0,1,1,1), (0,1,2,2) and 2 on the orbit of (0,2,2,2).
Claim: Phi(max) = -1, Phi(g) = 0 for every twin germ at a 4-tie (all labelings, all kappa).
Phi(g_kappa) is piecewise linear in kappa with kinks |kappa| <= 12 (grid entries <= 3), so checking
|kappa| <= 60 covers all integers."""
import itertools
def relu(x): return x if x > 0 else 0
orbs = {(0,0,0,0):1,(0,0,2,2):1,(0,1,1,1):1,(0,1,2,2):1,(0,2,2,2):2}
W = {}
for p, w in orbs.items():
    for q in set(itertools.permutations(p)): W[q] = w
cube = list(itertools.product([0,1], repeat=4))
def phi(f):
    return sum(w * sum((-1) ** (4 - sum(s)) * f([y[i] + s[i] for i in range(4)]) for s in cube) for y, w in W.items())
print('Phi(max) =', phi(max))
bad = 0
for k in range(-60, 61):
    for a, c, l1, l2 in itertools.permutations(range(4)):
        g = lambda z: relu(-z[a] + (1 - 2 * k) * z[c] + k * (z[l1] + z[l2]) + relu(z[l1] - z[c]) + relu(z[l2] - z[c]))
        if phi(g) != 0: bad += 1
print('nonzero on twin germs:', bad)
