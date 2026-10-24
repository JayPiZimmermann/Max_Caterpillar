"""Test structured labeling families: rotations of a word, etc."""
import sys, itertools
sys.argv = [sys.argv[0], sys.argv[1], sys.argv[2], '0', '0']
exec(open('fewperm.py').read().split('rng = random.Random(SEED)')[0])
base = tuple(range(N))
rots = [base[i:] + base[:i] for i in range(N)]
for t in range(1, N + 1):
    U = set()
    for pi in rots[:t]:
        U |= faces_of_pi(pi)
    print('first', t, 'rotations: |U|', len(U), 'feasible', feasible(U), flush=True)
# rotations plus reversals
revs = [tuple(reversed(p)) for p in rots]
U = set()
for pi in rots + revs: U |= faces_of_pi(pi)
print('rotations+reversals |U|', len(U), feasible(U))
