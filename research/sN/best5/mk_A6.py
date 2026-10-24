"""Model (A), h2 = 6: max_5 = relu(m01) - relu(-m01) + (4-neuron identity of
research/sN/dfs/h4-general-neurons/r2_spec_N5_k4.py).  Writes netA_h2_6.json."""
import json, runpy, os
from fractions import Fraction as Fr
from phiA import phi_rows, to_phi, net_json
spec = runpy.run_path(os.path.join(os.path.dirname(__file__), '../dfs/h4-general-neurons/r2_spec_N5_k4.py'))
N = 5
l, a = spec['R']
second, out = [to_phi(N, l, a), to_phi(N, [-c for c in l], {p: -c for p, c in a.items()})], [Fr(1), Fr(-1)]
for d, l, a in spec['NEURONS']:
    second.append(to_phi(N, l, a)); out.append(Fr(d))
json.dump(net_json(N, phi_rows(N), second, out), open('netA_h2_6.json', 'w'), indent=1)
print('written')
