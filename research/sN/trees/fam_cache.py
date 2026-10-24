#!/usr/bin/env python3
"""Cache sym_md families: fam_cache.py m R pred(two|twin) -> logs/fam_{pred}_{m}_{R}.pkl"""
import sys, pickle, time
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/research/sN/trees')
import sym_md
m, R, pr = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sym_md.MODE['pred'] = sym_md.twin_leaves if pr == 'twin' else sym_md.two_outleaves
t = time.time(); fam = sym_md.family(m, R)
pickle.dump(fam, open(f'logs/fam_{pr}_{m}_{R}.pkl', 'wb'))
print(m, R, pr, len(fam), f'{time.time()-t:.0f}s', flush=True)
