"""For a combination E = sum d_k U_k (pickle), and each coordinate a:
the units that are a+ / a- neutral (coefficient of x_a vanishes in the limit)
and depend on x_a; D_{[N]-a} of the limit combinations."""
import pickle, sys, itertools
from fractions import Fraction
d = pickle.load(open(sys.argv[1], 'rb'))['d']
N = len(next(iter(d))[0])
def limit(key, a, s):
    h, M = key
    c = h[a]; hh = list(h); MM = []
    for i, j in M:
        if a not in (i, j): MM.append((i, j)); continue
        # sigma(x_i - x_j)
        if (s > 0 and i == a) or (s < 0 and j == a):   # becomes linear x_i - x_j
            if i == a: c += 1; hh[j] -= 1
            else: c -= 1; hh[i] += 1
        # else -> 0
    hh[a] = 0
    return c, (tuple(hh), tuple(MM))
def Dset(key, S):
    h, M = key; tot = 0
    for r in range(len(S) + 1):
        for R in itertools.combinations(S, r):
            Rs = set(R)
            v = sum(h[i] for i in R) + sum(1 for i, j in M if i in Rs and j not in Rs)
            tot += (-1) ** (len(S) - r) * max(v, 0)
    return tot
def depends(key, a):
    h, M = key
    return h[a] != 0 or any(a in e for e in M)
for a in range(N):
    S = [i for i in range(N) if i != a]
    out = []
    for s in (+1, -1):
        neutral = [(k, v) for k, v in d.items() if depends(k, a) and limit(k, a, s)[0] == 0]
        Dv = sum(Fraction(v) * Dset(limit(k, a, s)[1], S) for k, v in neutral)
        out.append((len(neutral), sum(1 for k, v in neutral if Dset(limit(k, a, s)[1], S) != 0), Dv))
    print(f'a={a}: a+ neutral {out[0][0]} (D-active limits {out[0][1]}) D={out[0][2]} | a- neutral {out[1][0]} (D-active {out[1][1]}) D={out[1][2]}')
nu = {k: sum(1 for a in range(N) for s in (1, -1) if depends(k, a) and limit(k, a, s)[0] == 0) for k in d}
print('neutral counts per unit', sorted(nu.values()))
