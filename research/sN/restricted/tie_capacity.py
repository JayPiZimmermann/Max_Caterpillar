"""EXACT count: how many 3-top-tie localities (T, rho) one restricted-model neuron
relu(g), g in span(x_i, relu(x_i-x_j)), can serve.

Serve(g, T, rho): g vanishes identically on the face {x_T = s > x_rho(1) > ...}
and the germ relu(g^p) at a point of that face is not in V_T (+ linear), where
V_T = span of coordinates and hinges inside T.

Set-function form: f(S) = g(1_S).  g vanishes on the face iff f = 0 on the chain
T, T+rho1, ..., [N].  The germ on T is the Lovasz extension of f restricted to
subsets of T; relu of it is outside V_T iff either f changes strict sign along a
chain of subsets of T (a kink off the braid walls), or the top Moebius
coefficient sum_{A subset T} (-1)^{3-|A|} relu(f(A)) is nonzero.

Test neuron: g = sum_{q in Q} relu(x_q - x_a) - sum_{p in P} relu(x_p - x_a),
{a}, P, Q a partition of [N].  Prediction: serves exactly the triples {a,p,q}
with all (N-3)! orders, i.e. |P||Q|(N-3)! localities.
"""
import itertools, sys
from math import comb, factorial


def relu(t):
    return t if t > 0 else 0


def serves_count(N, f):
    total = 0
    triples = []
    for T in itertools.combinations(range(N), 3):
        Ts = set(T)
        # germ relevance
        sub = {}
        for r in range(4):
            for A in itertools.combinations(T, r):
                sub[frozenset(A)] = f(frozenset(A))
        cut = any(sub[A] * sub[B] < 0 for A in sub for B in sub if A < B)
        top = sum((-1) ** (3 - len(A)) * relu(v) for A, v in sub.items())
        if not (cut or top != 0):
            continue
        rest = [o for o in range(N) if o not in Ts]
        cnt = 0
        for rho in itertools.permutations(rest):
            S = set(Ts)
            ok = f(frozenset(S)) == 0
            for o in rho:
                if not ok:
                    break
                S.add(o)
                ok = f(frozenset(S)) == 0
            cnt += ok
        if cnt:
            triples.append(T)
        total += cnt
    return total, triples


def g_star(a, P, Q):
    def f(S):
        if a in S:
            return 0
        return sum(1 for q in Q if q in S) - sum(1 for p in P if p in S)
    return f


if __name__ == '__main__':
    for N in range(4, int(sys.argv[1]) + 1):
        a = 0
        others = list(range(1, N))
        h = len(others) // 2
        P, Q = others[:h], others[h:]
        tot, tr = serves_count(N, g_star(a, P, Q))
        allloc = comb(N, 3) * factorial(N - 3)
        print(N, 'served', tot, 'predicted', len(P) * len(Q) * factorial(N - 3),
              'all localities', allloc, 'ratio %.3f' % (allloc / tot))
