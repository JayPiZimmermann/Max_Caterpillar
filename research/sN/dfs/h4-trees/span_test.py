#!/usr/bin/env python3
"""Rank of class vocabularies and membership of max_N (branch h4-trees).
Usage: python span_test.py N mode [top]"""
import sys
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
import vocabulary_search as vs
import treeclass as tc
N = int(sys.argv[1]); mode = sys.argv[2]; top = len(sys.argv) > 3
K = sorted(k for k in tc.vocabulary(N, mode, top) if not tc.is_aux(k) and any(k[0]) or k[1])
aux = vs.aux_functions(N)
funcs = [('key', k) for k in K] + [('aux', a) for a in aux]
r0, ok0 = vs.exact_rank_fast(N, funcs)
r1, ok1 = vs.exact_rank_fast(N, funcs + [('max',)])
print(f'N={N} mode={mode} top={top}: {len(K)} keys (with hinges); rank(keys+aux)={r0} [{ok0}], '
      f'with max {r1} [{ok1}]; q = {r0 - len(aux)}; max in span: {r1 == r0}', flush=True)
