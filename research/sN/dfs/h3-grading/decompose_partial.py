"""Like decompose.py but with partial Young-subgroup data: solve m_lam from trivial twists for
mu in TRIV and sign twists for mu in SGN (upward closed in dominance), check all other records."""
import sys, json
from kostka import partitions, kostka, conj, flam
N = int(sys.argv[1]); TRIV = [tuple(map(int, s)) for s in sys.argv[2].split(',')]; SGN = [tuple(map(int, s)) for s in sys.argv[3].split(',')]
recs = [json.loads(l) for l in open(f'grade_{N}.log')]
Ps = list(partitions(N))
def pieces(r):
    rk = r['ranks_A_then_by_M']
    return [rk[0]] + [rk[i] - rk[i - 1] for i in range(1, len(rk))]
T = {tuple(r['mu']): pieces(r) for r in recs if r['twist'] == 'triv'}
S = {tuple(r['mu']): pieces(r) for r in recs if r['twist'] == 'sgn'}
np_ = len(next(iter(T.values())))
tot = {l: 0 for l in Ps}
for p in range(np_):
    m = {}
    for lam in Ps:
        if lam in TRIV:
            m[lam] = T[lam][p] - sum(kostka(l, lam) * m[l] for l in m)
    for mu in Ps:
        if mu in SGN:
            lam = conj(mu)
            assert lam not in m
            m[lam] = S[mu][p] - sum(kostka(conj(l), mu) * m[l] for l in m)
    assert set(m) == set(Ps), set(Ps) - set(m)
    checks = [(mu, 'triv', T[mu][p] == sum(kostka(l, mu) * m[l] for l in Ps)) for mu in T] + \
             [(mu, 'sgn', S[mu][p] == sum(kostka(conj(l), mu) * m[l] for l in Ps)) for mu in S]
    bad = [c for c in checks if not c[2]]
    if p > 0:
        for l in Ps: tot[l] += m[l]
    print(f"piece {p} dim {sum(flam(l)*m[l] for l in Ps):6d} checks {len(checks)} bad {bad} " + ' '.join(f"{''.join(map(str,l))}:{m[l]}" for l in Ps))
print(f"V/A dim {sum(flam(l)*tot[l] for l in Ps)} " + ' '.join(f"{''.join(map(str,l))}:{tot[l]}" for l in Ps))
