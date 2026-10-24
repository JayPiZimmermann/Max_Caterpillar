"""Enumerate triples (up to S5 and order) of vanishing flats that contain all five 4-sets
(like every neuron of the known 4-neuron identity) and jointly cover all 20 3-localities.
Writes sub_triples.pkl."""
import itertools, pickle
from k2_exact import REL, IDX, cov, permZ, PERMS, F
FOURMASK = sum(1 << IDX[S] for S in REL if len(S) == 4)
TRI = [i for i, S in enumerate(REL) if len(S) == 3]
flats = []
for sub in range(1 << 10):
    Z = FOURMASK | sum(1 << TRI[b] for b in range(10) if sub >> b & 1)
    # keep only closed flats with nonzero space whose closure is Z
    from flats_loc import closure
    cl, B = closure(Z)
    if cl == Z and B:
        flats.append(Z)
cv = {Z: sum(1 << q for q in cov(Z)) for Z in flats}
print('subfamily flats', len(flats))
seen = set(); out = []
for a, b, c in itertools.combinations_with_replacement(flats, 3):
    if cv[a] | cv[b] | cv[c] != (1 << 20) - 1: continue
    key = min(tuple(sorted((permZ(a, p), permZ(b, p), permZ(c, p)))) for p in PERMS)
    if key not in seen:
        seen.add(key); out.append(key)
print('covering triples up to S5:', len(out))
pickle.dump(out, open('sub_triples.pkl', 'wb'))
