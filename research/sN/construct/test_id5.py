import sys; sys.path.insert(0, '../dfs/h4-general-neurons')
import runpy
from chambers import evaluate, top_of
s = runpy.run_path('../dfs/h4-general-neurons/r2_spec_N5_k4.py')
ok, bad, pieces = evaluate(5, s['NEURONS'])
print('braidPL', ok, len(bad), 'top', top_of(5, pieces))
for k in range(4):
    nn = [n for i, n in enumerate(s['NEURONS']) if i != k]
    ok, bad, p = evaluate(5, nn); print('drop', k, ok, len(bad))
