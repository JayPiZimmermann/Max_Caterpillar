"""Count pairs/triples of vanishing flats whose locality coverage is complete (exact bitmask logic).
Locality L=(T,o1): covered by flat Z iff T in Z and T+{o1} in Z."""
import pickle, itertools, collections
d = pickle.load(open('flats_loc.pkl', 'rb')); REL = d['REL']; flats = d['flats']
idx = {S: i for i, S in enumerate(REL)}
LOCS = [(T, o) for T in REL if len(T) == 3 for o in range(5) if o not in T]
def cov(Z):
    m = 0
    for q, (T, o) in enumerate(LOCS):
        if Z >> idx[T] & 1 and Z >> idx[T | {o}] & 1:
            m |= 1 << q
    return m
FULL = (1 << len(LOCS)) - 1
bymask = collections.defaultdict(list)
for Z, (dim, B) in flats.items():
    if dim > 0:
        bymask[cov(Z)].append(Z)
masks = list(bymask)
print('localities', len(LOCS), 'nonzero flats', sum(len(v) for v in bymask.values()), 'distinct coverage masks', len(masks))
# maximal masks
mx = [m for m in masks if not any(m != n and m | n == n for n in masks)]
print('maximal coverage masks', len(mx), 'max size', max(bin(m).count('1') for m in masks))
pairs = [(a, b) for i, a in enumerate(masks) for b in masks[i:] if a | b == FULL]
print('covering mask pairs', len(pairs), 'flat pairs', sum(len(bymask[a]) * len(bymask[b]) for a, b in pairs))
pickle.dump({'LOCS': LOCS, 'bymask': dict(bymask), 'pairs': pairs}, open('cover_pairs.pkl', 'wb'))
