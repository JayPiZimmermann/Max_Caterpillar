"""Count ordered triples of nonzero vanishing flats whose locality coverage is complete
(and, separately, also covering all five 4-sets), by subset transforms over 2^20."""
import pickle, numpy as np
from k2_exact import IDX, REL
c = pickle.load(open('cover_pairs.pkl', 'rb')); bymask = c['bymask']
FULL = (1 << 20) - 1
cnt = np.zeros(1 << 20, np.int64)
for m, Zs in bymask.items(): cnt[m] += len(Zs)
# g(Q) = #flats with mask & Q == 0  = sum over masks subset of comp(Q) -> subset-sum transform
s = cnt.copy()
for i in range(20):
    bit = 1 << i; idx = np.arange(1 << 20); sel = (idx & bit) != 0
    s[sel] += s[idx[sel] ^ bit]
g = s[FULL ^ np.arange(1 << 20)]          # g[Q] = sum_{m subset of comp(Q)} cnt[m]
f = (g.astype(object) ** 2) if False else g * g   # pairs avoiding Q (fits in int64? up to 1e9)
# h(R) = sum_{Q subset R} (-1)^|Q| f(Q)
pc = np.array([bin(q).count('1') & 1 for q in range(1 << 20)])
h = np.where(pc == 1, -f, f)
for i in range(20):
    bit = 1 << i; idx = np.arange(1 << 20); sel = (idx & bit) != 0
    h[sel] += h[idx[sel] ^ bit]
tot = sum(len(Zs) * int(h[FULL ^ m]) for m, Zs in bymask.items())
print('ordered triples of flats with complete 3-locality coverage:', tot, ' /(6*120) ~', tot // 720)
