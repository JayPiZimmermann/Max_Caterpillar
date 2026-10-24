"""Which ray classes carry local conditions not implied by the codim-2
(3,1)-straightness conditions?  usage: combo.py N [p]
Ambient W_N (germs2.Setup).  Rows mod p restricted to W (row @ BW)."""
import pickle, random, sys, time
from math import gcd
import numpy as np
sys.path.insert(0, '..')
from germs2 import Setup, PR, rref, rays, canon, rank_big
from germ2d import Germs, dot, nullspace

N = int(sys.argv[1]); p = int(sys.argv[2]) if len(sys.argv) > 2 else PR
t0 = time.time()
S = Setup(N, p)
G = Germs(N)
res = pickle.load(open(f'analyze_{N}.pkl', 'rb'))
classes = pickle.load(open(f'faces_{N}.pkl', 'rb'))
dimV = rank_big(S.Vmat, p)
print('dimW', S.dimW, 'dimV', dimV, f'{time.time()-t0:.0f}s', flush=True)


def face_row(x0):
    Hs, u, v, rs = G.rays2d(x0)
    Bv = 1 + max(abs(dot(h, r[0])) for h in G.hyps for r in rs)
    lin = [[r[0][i] - r[0][0] for r in rs] for i in range(1, N)]
    bumps = [[abs(dot(h, r[0])) for r in rs] for h in Hs]
    ann = nullspace(lin + bumps, len(rs))
    rows = []
    for cvec in ann:
        den = 1
        for x in cvec:
            den = den * x.denominator // gcd(den, x.denominator)
        ci = [int(x * den) for x in cvec]
        base = [Bv * a for a in x0]
        row = np.zeros(S.A.nvars, dtype=np.int64)
        for cc, r in zip(ci, rs):
            for k, x in S.eval_row([a + b for a, b in zip(base, r[0])]).items():
                row[k] = (row[k] + cc * x) % p
        tot = sum(ci)
        for k, x in S.eval_row(base).items():
            row[k] = (row[k] - tot * x) % p
        rows.append(row)
    return rows


rows = []
for c, d in res.items():
    if d['k'] == 3 and d['nb'] == 1:
        for x0 in classes[c]:
            rows += face_row(x0)
R2 = (np.array(rows) % p) @ S.BW % p
acc, _ = rref(R2, p)
print('codim-2 condition rank in W', acc.shape[0], ' needed', S.dimW - dimV, f'{time.time()-t0:.0f}s', flush=True)
pickle.dump(acc, open(f'codim2rows_{N}_{p}.pkl', 'wb'))
R = rays(N, S.H + S.braid)
rcl = {}
for x in R:
    rcl.setdefault(canon(x), []).append(x)
rng = random.Random(1)
base = acc.shape[0]
for c in sorted(rcl, key=lambda c: -len(rcl[c])):
    xs = rcl[c]
    _, rW, rV = S.local_conditions(xs[0], rng)
    if rW == rV:
        continue
    new = [S.local_conditions(x, rng)[0] for x in xs]
    test, _ = rref(np.concatenate([acc] + new), p)
    gain = test.shape[0] - acc.shape[0]
    print('ray class', c, 'orbit', len(xs), 'germ W,V', (rW, rV), 'new rank', gain, f'{time.time()-t0:.0f}s', flush=True)
    if gain:
        acc = test
print('final rank', acc.shape[0], 'needed', S.dimW - dimV)
