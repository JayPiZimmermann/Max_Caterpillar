"""Generate LocalFour.lean: kernel-checked certificate that every pair of structural
4-locality germs is killed by one of the stencils in cert4.json (D max = -1 each).
Germ list in Lean is the full structural enumeration (not filtered by fullness)."""
import json, itertools
cert = json.load(open('cert4.json'))
st = cert['stencils']
def relu(x): return x if x > 0 else 0
def germs():
    out = []
    for a in range(4):
        R = [t for t in range(4) if t != a]
        for vr in itertools.product(range(-1, 4), repeat=3):
            if sum(vr) != 1: continue
            v = [0] * 4; v[a] = -1
            for t, x in zip(R, vr): v[t] = x
            und = [(R[0], R[1]), (R[0], R[2]), (R[1], R[2])]
            for r in range(3):
                for E in itertools.combinations(und, r):
                    for ori in itertools.product([0, 1], repeat=r):
                        M = [(e if o == 0 else (e[1], e[0])) for e, o in zip(E, ori)]
                        out.append((v, M))
    return out
def ev(g, z):
    v, M = g
    return relu(sum(a * b for a, b in zip(v, z)) + sum(relu(z[p] - z[c]) for p, c in M))
def D(s, f):
    tot = 0
    for S in range(16):
        z = [s['base'][i] + (s['steps'][i] if S >> i & 1 else 0) for i in range(4)]
        tot += (-1) ** (4 - bin(S).count('1')) * f(z)
    return tot
G = germs()
pats = sorted({tuple(D(s, lambda z: ev(g, z)) == 0 for s in st) for g in G})
print('structural germs', len(G), 'distinct kill patterns', len(pats))
assert all(any(a and b for a, b in zip(p, q)) for p in pats for q in pats)
assert all(D(s, max) == -1 for s in st)
