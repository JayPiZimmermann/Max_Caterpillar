"""Global kink hyperplanes of Sigma_N from the units (all cells).  Saves hyps_N.pkl"""
import pickle, sys, itertools
sys.path.insert(0, '..')
from ambient import units_of, primitive
N = int(sys.argv[1])
U = units_of(N)
H = set()
perms = list(itertools.permutations(range(N)))
for (h, M) in U:
    Ml = list(M)
    for pi in perms:
        pos = {v: r for r, v in enumerate(pi)}
        g = list(h)
        for (s, t) in Ml:
            if pos[s] > pos[t]:
                g[s] += 1; g[t] -= 1
        # crossing: gap form mixed
        suff, pos_, neg_ = 0, False, False
        for v in reversed(pi[1:]):
            suff += g[v]
            if suff > 0: pos_ = True
            if suff < 0: neg_ = True
        if pos_ and neg_:
            H.add(primitive(tuple(g))[0])
pickle.dump(sorted(H), open(f'hyps_{N}.pkl', 'wb'))
from bends import family
F = set(family(N))
print(N, 'unit kink hyperplanes', len(H), 'family', len(F), 'H<=F', H <= F, 'F<=H', F <= H)
