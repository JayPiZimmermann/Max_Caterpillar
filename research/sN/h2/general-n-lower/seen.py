r"""Exact 3-locality 'seen' sets for one general second-layer neuron (cube functional).

Neuron preactivation (reduced model, see NOTE.md):  G(z) = sum_i gam_i z_i + sum_{i<j} c_ij max(z_i, z_j),
arbitrary rational gam, c (c signed).  Gam_v := gam_v + deg(v), deg(v) = sum_j c_vj.
Locality L = (T, rho): T a 3-set tied on top, O = V\T strictly ordered below by rho.
Combinatorial test (proved in NOTE.md):  seen(L) iff
  (a) for all o in O: sum_{j in T or above o} c_oj = Gam_o,
  (c) sum_{t in T} Gam_t = c(E(T)),
  (L) Lam = sum_{t in T} [relu(Gam_t) - relu(d_t - Gam_t)] != 0,   d_t = c(t, T\\t).
Brute-force test: evaluate G on N-2 independent points of the cell (vanishing), then
the 8-corner mixed difference of relu(G) at a generic cell point.  Exact Fractions.
"""
import itertools, math
from fractions import Fraction as Fr


def relu(t):
    return t if t > 0 else 0


class Neuron:
    def __init__(self, N, gam, c):
        self.N, self.gam = N, [Fr(v) for v in gam]
        self.c = [[Fr(0)] * N for _ in range(N)]
        for (i, j), w in c.items():
            self.c[i][j] = self.c[j][i] = Fr(w)
        self.deg = [sum(self.c[v]) for v in range(N)]
        self.Gam = [self.gam[v] + self.deg[v] for v in range(N)]

    def G(self, z):
        N = self.N
        v = sum(self.gam[i] * z[i] for i in range(N))
        for i in range(N):
            for j in range(i + 1, N):
                if self.c[i][j]:
                    v += self.c[i][j] * max(z[i], z[j])
        return v

    # ---- combinatorial test
    def good_T(self, T):
        c, Gam = self.c, self.Gam
        cE = c[T[0]][T[1]] + c[T[0]][T[2]] + c[T[1]][T[2]]
        if sum(Gam[t] for t in T) != cE:
            return False
        lam = 0
        for t in T:
            d = sum(c[t][u] for u in T if u != t)
            lam += relu(Gam[t]) - relu(d - Gam[t])
        return lam != 0

    def valid_order(self, T, order):
        above = list(T)
        for o in order:
            if sum(self.c[o][j] for j in above) != self.Gam[o]:
                return False
            above.append(o)
        return True

    def n_valid_orders(self, T):
        """# orders of O valid for (a): DP over the set B already placed at the bottom."""
        O = [v for v in range(self.N) if v not in T]
        m = len(O)
        cnt = {0: 1}
        for _ in range(m):
            new = {}
            for S, k in cnt.items():
                for i in range(m):
                    if S >> i & 1:
                        continue
                    o = O[i]
                    # o is placed just above the set S (S = vertices below o)
                    up = self.deg[o] - sum(self.c[o][O[j]] for j in range(m) if S >> j & 1)
                    if up == self.Gam[o]:
                        new[S | 1 << i] = new.get(S | 1 << i, 0) + k
            cnt = new
        return cnt.get((1 << m) - 1, 0)

    def W(self):
        return sum(self.n_valid_orders(T) for T in itertools.combinations(range(self.N), 3) if self.good_T(T))

    def f(self):
        return Fr(self.W(), math.factorial(self.N - 3))

    # ---- brute force
    def seen_brute(self, T, order, rng):
        N = self.N
        def cellpt():
            vals = sorted((Fr(rng.randint(1, 10**6), 997) for _ in range(N - 2)), reverse=True)
            z = [Fr(0)] * N
            for t in T:
                z[t] = vals[0] + 1
            for o, v in zip(order, vals[1:]):
                z[o] = v
            return z
        for _ in range(N):  # N random points: vanishing on all <=> vanishing on cell (w.h.p.; linear on cell)
            if self.G(cellpt()) != 0:
                return False
        p = cellpt()
        gaps = [p[T[0]] - p[order[0]]] if order else []
        gaps += [p[order[i]] - p[order[i + 1]] for i in range(len(order) - 1)]
        delta = min(gaps + [Fr(1)]) / 4
        lam = 0
        for S in itertools.product([0, 1], repeat=3):
            z = list(p)
            for t, s in zip(T, S):
                z[t] += delta * s
            lam += (-1) ** (3 - sum(S)) * relu(self.G(z))
        return lam != 0

    def seen_comb(self, T, order):
        return self.good_T(T) and self.valid_order(T, order)


def localities(N):
    for T in itertools.combinations(range(N), 3):
        O = [v for v in range(N) if v not in T]
        for order in itertools.permutations(O):
            yield T, order


def star(N, center, w):
    """Signed star: G = sum_v w_v max(z_center, z_v) - (sum w) z_center."""
    c = {(min(center, v), max(center, v)): w[v] for v in range(N) if v != center and w[v]}
    gam = [0] * N
    gam[center] = -sum(c.values())
    return Neuron(N, gam, c)
