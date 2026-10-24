"""Model (A) network from a free-remainder spec (r2_certify format):
max_5 = relu(R) - relu(-R) + sum_k d_k relu(g_k) on the paper's first layer Phi.
Usage: python mk_from_spec.py spec.py out.json"""
import sys, json, runpy
from fractions import Fraction as Fr
from phiA import phi_rows, to_phi, net_json
spec = runpy.run_path(sys.argv[1]); N = spec['N']
l, a = spec['R']
second = [to_phi(N, l, a), to_phi(N, [-c for c in l], {p: -c for p, c in a.items()})]; out = [Fr(1), Fr(-1)]
for d, l, a in spec['NEURONS']:
    second.append(to_phi(N, l, a)); out.append(Fr(d))
json.dump(net_json(N, phi_rows(N), second, out), open(sys.argv[2], 'w'), indent=1)
print('h2 =', len(second))
