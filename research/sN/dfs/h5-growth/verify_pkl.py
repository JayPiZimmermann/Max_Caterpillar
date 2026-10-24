"""Independent fine-cell certificate for a stored expansion support.
usage: python verify_pkl.py N file.pkl  -> prints support size and whether
scripts/vocabulary_search.exact_expansion finds and verifies an exact expansion
of max_N on exactly that support (cell-wise exact identity check)."""
import pickle, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', '..', 'scripts'))
import vocabulary_search as vs
N = int(sys.argv[1]); D = pickle.load(open(sys.argv[2], 'rb'))
K = list(D['K'])
assert all(not vs.is_auxiliary(k) for k in K)
K0, _ = vs.dictionary(N); K0 = set(K0)
assert all(k in K0 for k in K)
res = vs.exact_expansion(N, K)
print(sys.argv[2], 'support', len(K), 'certified expansion:', res is not None)
if res is not None:
    d, e = res
    print('nonzero unit coefficients', sum(1 for v in d.values() if v != 0))
