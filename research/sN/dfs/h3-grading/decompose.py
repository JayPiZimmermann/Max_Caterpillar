"""Decompose A_N and the graded pieces gr_j = F_j/F_{j-1} (F_j = A_N + span{U_k: |M_k| <= j}) into
S_N irreducibles from grade_N.log, using trivial twists (all mu) and checking with sign twists."""
import sys, json
from kostka import partitions, kostka, conj, flam, solve
N = int(sys.argv[1])
recs = [json.loads(l) for l in open(f'grade_{N}.log')]
Ps = list(partitions(N))
def pieces(r):
    rk = r['ranks_A_then_by_M']
    return [rk[0]] + [rk[i] - rk[i - 1] for i in range(1, len(rk))]
T = {tuple(r['mu']): pieces(r) for r in recs if r['twist'] == 'triv'}
S = {tuple(r['mu']): pieces(r) for r in recs if r['twist'] == 'sgn'}
npieces = len(next(iter(T.values())))
names = ['A_N'] + [f'gr|M|={j}' for j in range(npieces - 1)]
tot = {l: 0 for l in Ps}
for p in range(npieces):
    m = solve(N, {mu: T[mu][p] for mu in T})
    ok = all(S[mu][p] == sum(kostka(conj(l), mu) * m[l] for l in Ps) for mu in S)
    dim = sum(flam(l) * m[l] for l in Ps)
    if p > 0:
        for l in Ps: tot[l] += m[l]
    print(f"{names[p]:10s} dim {dim:6d} sgn-check {ok}  " + ' '.join(f"{''.join(map(str,l))}:{m[l]}" for l in Ps if m[l]))
print(f"{'V/A':10s} dim {sum(flam(l)*tot[l] for l in Ps):6d}       " + ' '.join(f"{''.join(map(str,l))}:{tot[l]}" for l in Ps if tot[l]))
