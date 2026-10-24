import runpy, itertools
from fractions import Fraction as Fr
from chambers import lin_on, classify
s = runpy.run_path('../dfs/h4-general-neurons/r2_spec_N5_k4.py')
core = s['NEURONS'][1:]
names = ['AQ', 'u', 'v']
from collections import defaultdict
stats = defaultdict(list)
for rank in itertools.permutations(range(5)):
    cr = []
    for nm, (d, l, W) in zip(names, core):
        a, pos = lin_on(5, rank, l, W)
        kind, key, lam = classify(5, rank, a)
        if kind == 'cross': cr.append((nm, key, lam * d))
    if cr: stats[tuple(sorted(c[0] for c in cr))].append((rank, [(c[0], tuple(str(k) for k in c[1]), str(c[2])) for c in cr]))
for k, v in stats.items():
    print(k, len(v))
    for r in v[:3]: print('   ', r)
