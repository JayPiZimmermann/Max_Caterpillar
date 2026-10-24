"""W'_m(N) = max over units of sum_T p_T over localities with A_k(p_L)=0 and germ not
auxiliary (germ classification via local.quotient mod P; class set is small)."""
import sys, itertools, time, math
from fractions import Fraction
from germs import localities, relabel
from local import full_matrix, quotient_modp
m = int(sys.argv[1]); N = int(sys.argv[2])
t0 = time.time()
rec = list(localities(N, m))
G = sorted({g for *_, g in rec}, key=lambda k: (sorted(k[1]), k[0]))
A, naux = full_matrix(m, G)
Q = quotient_modp(A, naux)
isaux = {g: not Q[:, i].any() for i, g in enumerate(G)}
W = {}
for uid, cfg, T, c, g in rec:
    if not isaux[g]:
        W[uid] = W.get(uid, 0) + Fraction(c, math.factorial(N - m))
best = max(W.values())
arg = [u for u in W if W[u] == best][:3]
print(f"N={N} m={m}: W'={best} ({float(best):.4f}) bound t*C(N,m)/W' = t*{math.comb(N,m)/best:.4f}; germs {len(G)} aux-germs {sum(isaux.values())} ({time.time()-t0:.1f}s)")
hist = {}
for w in W.values(): hist[w] = hist.get(w, 0) + 1
print('  hist top', sorted(hist.items(), key=lambda kv: -kv[0])[:6])
for u in arg:
    print('  arg', [ (cfg, T, c, g) for uid, cfg, T, c, g in rec if uid == u and not isaux[g]][:12])
