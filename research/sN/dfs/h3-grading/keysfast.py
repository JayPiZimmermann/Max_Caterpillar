"""Fast dictionary: K_0(N) = union over sigma in S_N of sigma . K_0(pi = id).  Cross-checked
against common.keys (vocabulary_search.dictionary) for N <= 6; writes keys_N.pkl in the same format."""
import sys, os, pickle, itertools, time
from common import vs, HERE
from sym import act_key
N = int(sys.argv[1])
t0 = time.time()
base = set()
pid = tuple(range(N))
for size in range(1, N - 1):
    for S in itertools.combinations(range(1, N - 1), size):
        base |= vs.normalized_faces(N, pid, frozenset(S))
base = {k for k in base if not vs.is_auxiliary(k)}
allk = set()
for g in itertools.permutations(range(N)):
    for k in base:
        allk.add(act_key(g, k))
ks = sorted(allk, key=lambda k: (k[0], sorted(k[1])))
print(N, 'base', len(base), 'keys', len(ks), round(time.time() - t0, 1), flush=True)
fn = os.path.join(HERE, f'keys_{N}.pkl')
if os.path.exists(fn):
    old = pickle.load(open(fn, 'rb'))
    print('matches common.keys:', old == ks)
else:
    pickle.dump(ks, open(fn, 'wb'))
