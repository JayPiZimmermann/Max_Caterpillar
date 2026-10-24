import pickle, sys, itertools
d = pickle.load(open(sys.argv[1], 'rb'))['d']
N = len(next(iter(d))[0])
def norm(h, pairs):
    h = list(h); M = []
    for a, b in pairs:
        if a > b: h[a] += 1; h[b] -= 1; a, b = b, a
        M.append((a, b))
    return (tuple(h), frozenset(M))
def pk(key, p):
    h, M = key; h2 = [0]*N
    for i in range(N): h2[p[i]] = h[i]
    return norm(h2, [(p[a], p[b]) for a, b in M])
for p in itertools.permutations(range(N)):
    d2 = {pk(k, p): v for k, v in d.items()}
    if d2 == d: print('stabilizer', p)
    elif set(d2) == set(d): print('support-stabilizer', p)
