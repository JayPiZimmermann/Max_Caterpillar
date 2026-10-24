#!/usr/bin/env python3
"""Unit-cube formulation.  U_y f = MD of f on the unit cube anchored at y.  Every MD functional on
diagonal-invariant germs is Phi_W f = sum_{ybar in Z^m / Z 1} W(ybar) U_ybar f, Phi_W(max) = (-1)^(m+1) W(0).
Unknowns: symmetric W on normalised anchors (min 0, entries <= k).  Constraints: Phi_W(g) = 0 for twin germs.
Usage: twin_wbar.py m k R [maxsupp]"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
from twin_lib import eval_germ, orbit, rank_mod_p
from fractions import Fraction


def anchors(m, k):
    reps = [p for p in itertools.combinations_with_replacement(range(k + 1), m) if p[0] == 0]
    return reps


def ufeat(m, reps, fn):
    cube = np.array(list(itertools.product([0, 1], repeat=m)), dtype=np.int64)
    sign = np.array([(-1) ** (m - int(s.sum())) for s in cube], dtype=np.int64)
    out = []
    for p in reps:
        Y = np.array(orbit(p), dtype=np.int64)
        Z = (Y[:, None, :] + cube[None, :, :]).reshape(-1, m)
        out.append(int((fn(Z).reshape(len(Y), len(cube)) @ sign).sum()))
    return out
