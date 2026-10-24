"""Third-mixed-difference detectors Lambda_{(a,b,rho)} on path units (all apexes).
Units: (apex, path) with path ending at 'end'. Test point for (a, b, rho):
rho = order of the N-2 other labels; z_{rho_j} = 4j (j=1..N-2), z_a = z_b = 4(N-2);
c = rho_{N-2}; corners add 1 (s=1/4 after scaling) to coords a, b, c."""
import itertools, sys, numpy as np
from rank import rank_mod

def unit(apex, path, x):
    v = x[path[-1]] - x[apex]
    for p, q in zip(path, path[1:]):
        v += max(x[p] - x[q], 0)
    return max(v, 0)

def lam(N, a, b, rho, f):
    c = rho[-1]
    z = [0] * N
    for j, l in enumerate(rho): z[l] = 4 * (j + 1)
    z[a] = z[b] = 4 * (N - 2)
    tot = 0
    for e in itertools.product((0, 1), repeat=3):
        x = z[:]
        x[a] += e[0]; x[b] += e[1]; x[c] += e[2]
        tot += (-1) ** sum(e) * f(x)
    return tot

def units(N, apexes=None):
    out = []
    seen = set()
    for a in (apexes if apexes is not None else range(N)):
        for p in itertools.permutations([i for i in range(N) if i != a]):
            key = (a, min(p, p[::-1]))
            if key in seen: continue
            seen.add(key); out.append((a, list(p)))
    return out

def dets(N, apexes=None):
    out = []
    for a in (apexes if apexes is not None else range(N)):
        for b in range(N):
            if b == a: continue
            for rho in itertools.permutations([i for i in range(N) if i not in (a, b)]):
                out.append((a, b, list(rho)))
    return out

if __name__ == "__main__":
    N = int(sys.argv[1])
    for ap in ([0], None):
        U = units(N, ap); D = dets(N, ap)
        M = np.array([[lam(N, a, b, rho, lambda x: unit(u[0], u[1], x)) for u in U] for (a, b, rho) in D], dtype=np.int64)
        print(N, "apexes", ap, "units", len(U), "detectors", len(D), "rank", rank_mod(M), flush=True)
