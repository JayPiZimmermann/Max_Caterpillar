"""Exact codim-2 germ classification.  usage: analyze.py N
For every class of codim-2 faces: k = #hyperplanes through it, nb = #braid
among them, W-germ nonlinear dim = 2k-2 if nb >= 1 else k (balanced weights;
straight kinks inside an open braid cell), V-germ nonlinear dim (exact rank of
values on the 2k rays minus 2).  Defect = W - V = number of local conditions."""
import pickle, sys, time
from collections import Counter
from germ2d import Germs, dot, rank, nullspace, weights_from_values

N = int(sys.argv[1])
G = Germs(N)
classes = pickle.load(open(f'faces_{N}.pkl', 'rb'))
t0 = time.time()
res = {}
for c, pts in sorted(classes.items()):
    x0 = pts[0]
    Hs, u, v, rays = G.rays2d(x0)
    k = len(Hs)
    nb = sum(1 for h in Hs if h in G.braid)
    B = 1 + max(abs(dot(h, r[0])) for h in G.hyps for r in rays)
    rows = [G.germ(f, x0, rays, B) for f in G.funcs]
    rV = rank(rows) - 2
    rW = 2 * k - 2 if nb else k
    # straight part: for each line, is its straight bump in the V germ?
    res[c] = dict(orbit=len(pts), k=k, nb=nb, rW=rW, rV=rV, hyps=Hs)
print('time', f'{time.time()-t0:.1f}s')
tot = 0
summary = Counter()
for c, d in sorted(res.items(), key=lambda t: (t[1]['rW'] - t[1]['rV'], t[0])):
    summary[(d['k'], d['nb'], d['rW'], d['rV'])] += d['orbit']
    if d['rW'] != d['rV']:
        tot += d['orbit'] * (d['rW'] - d['rV'])
        print(c, 'orbit', d['orbit'], 'k', d['k'], 'braid', d['nb'], 'W', d['rW'], 'V', d['rV'], d['hyps'])
print('summary (k, nb, W, V): #faces')
for key, n in sorted(summary.items()):
    print('  ', key, n)
print('total local conditions (with multiplicity, before rank):', tot)
pickle.dump(res, open(f'analyze_{N}.pkl', 'wb'))
