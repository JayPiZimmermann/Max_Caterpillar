"""Exact (Fractions): given a list of localities, compute the subspace of braid neurons
vanishing on all their cones, a random element, its closure, and germ status per T."""
import sys, random, ast
from fractions import Fraction as Fr
from braidlib import *
def analyse(N, m, S, seed=0, show=True):
    LOC = list(localities(N, m)); n = nvars(N)
    rows = [r for L in S for r in cone_rows(N, *L)]
    B = nullspace(rows, n)
    random.seed(seed)
    th = [sum(Fr(random.randint(-30, 30))*b[i] for b in B) for i in range(n)]
    van = [L for L in LOC if all(sum(r[i]*th[i] for i in range(n)) == 0 for r in cone_rows(N, *L))]
    good = [L for L in van if mixed_diff_sigma(*germ(N, L[0], th), L[0]) != 0]
    if show:
        P = pidx(N)
        w = {p: th[k] for p, k in P.items() if th[k] != 0}
        kappa = [th[1+o] + sum(th[P[(o, j)]] for j in range(o+1, N)) for o in range(N)]
        print("dim", len(B), "vanish", len(van), "good", len(good), "goodT", sorted(set(L[0] for L in good)))
        print(" b", th[0], "w", {p: str(x) for p, x in w.items()}, "kappa", [str(x) for x in kappa])
    return th, van, good
if __name__ == "__main__":
    N = int(sys.argv[1]); m = int(sys.argv[2])
    S = ast.literal_eval(sys.argv[3])
    for s in range(3): analyse(N, m, S, seed=s)
