import itertools, runpy
from fractions import Fraction as Fr
from chambers import evaluate, top_of
s = runpy.run_path('../dfs/h4-general-neurons/r2_spec_N5_k4.py')
core = s['NEURONS'][1:]
def lift(neur, c, n=6):
    d, l, W = neur
    l2 = list(l) + [0] * (n - len(l)); W2 = dict(W)
    for j, cj in enumerate(c):
        if cj: W2[(n - 1, j)] = W2.get((n - 1, j), 0) + cj
    return (d, l2, W2)
ok, bad, pieces = evaluate(5, core); print('core n5 braidPL', ok, 'top', top_of(5, pieces))
for c in [(1,1,1,1,1), (-1,-1,-1,-1,-1), (1,0,0,0,0), (0,1,0,0,0), (Fr(1,10),)*5]:
    F = [lift(nn, c) for nn in core]
    ok, bad, pieces = evaluate(6, F)
    print(c, 'braidPL', ok, 'bad', len(bad))
