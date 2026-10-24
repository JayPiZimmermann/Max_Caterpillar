"""Is max_N in F_{N-3} = A_N + span{U_k : |M_k| <= N-3}?  Mod-p rank at random integer points (measured;
'not in' is robust: a rank increase mod p implies an increase over Q)."""
import sys, numpy as np
from common import keys
from sym import eval_keys, eval_aux, run_rank
import vocabulary_search as vs
for N in map(int, sys.argv[1:]):
    ks = [k for k in keys(N) if len(k[1]) <= N - 3]
    auxs = vs.aux_functions(N)
    rng = np.random.default_rng(5)
    X = rng.integers(-10**5, 10**5, size=(len(ks) + len(auxs) + 40, N), endpoint=True).astype(np.int64)
    blocks = [np.vstack([eval_aux(auxs, X), X.T, eval_keys(ks, X)]), X.max(1)[None, :]]
    print(N, 'rank F_{N-3}, +max:', run_rank(blocks, f'maxlow{N}'))
