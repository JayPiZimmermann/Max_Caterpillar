"""Numerical check of the dictionary between Brunck et al. Sec. 7.1 and our caterpillars.

Independent route: vertices of B_{v,pi,M} are enumerated from the inequality
description (Eq. (3) of arXiv:2610.28587v1) by solving all tight subsystems;
the support function of pyr_{e_v}(B) is the max over those vertices and e_v.
Compared with
  (a) the zonotope e_{pi_q} + sum_i [0, e_{pi_r(i)} - e_{pi_i}]  (vertex sets),
  (b) y_v + relu(y_{pi_q} - y_v + sum_i relu(y_{pi_r(i)} - y_{pi_i})),
  (c) the paper word (apex v, labels pi, cut set S = M - 1): head x_{pi(q+1)} - x_{pi(0)},
      edges x_{pi(p(j)+1)} - x_{pi(j+1)}, 1 <= j <= r.
Positions of Brunck et al. are 1-based: pi = (pi_1,...,pi_{n-1}).
"""
import itertools, random
import numpy as np

relu = lambda t: max(0.0, t)

def B_vertices(n, v, pi, M):
    # variables p in R^n; equalities p_v = 0, sum p = 1
    E = [np.eye(n)[v], np.ones(n)]; e = [0.0, 1.0]
    P = lambda i: pi[i - 1]  # 1-based position -> coordinate
    ineq = []  # (a, lo, hi): lo <= a.p <= hi
    for i in range(2, n):
        if i in M:
            a = np.zeros(n)
            for j in range(1, i): a[P(j)] += 1
            ineq.append((a, 0.0, 1.0))
        else:
            a = np.zeros(n); a[P(i)] = 1
            ineq.append((a, -1.0, 0.0))
    rows = []
    for a, lo, hi in ineq: rows += [(a, lo), (a, hi)]
    verts = []
    for T in itertools.combinations(range(len(rows)), n - 2):
        A = np.array(E + [rows[t][0] for t in T]); b = np.array(e + [rows[t][1] for t in T])
        if abs(np.linalg.det(A)) < 1e-9: continue
        p = np.linalg.solve(A, b)
        if all(lo - 1e-9 <= a @ p <= hi + 1e-9 for a, lo, hi in ineq):
            if not any(np.allclose(p, w) for w in verts): verts.append(p)
    return verts

def zono_vertices(n, v, pi, M):
    P = lambda i: pi[i - 1]
    q = max({1} | set(M))
    rr = lambda i: max({1} | {j for j in M if j < i})
    gens = []
    for i in range(2, n):
        g = np.zeros(n); g[P(rr(i))] += 1; g[P(i)] -= 1; gens.append(g)
    base = np.zeros(n); base[P(q)] = 1
    pts = []
    for eps in itertools.product([0, 1], repeat=len(gens)):
        p = base + sum((t * g for t, g in zip(eps, gens)), np.zeros(n))
        if not any(np.allclose(p, w) for w in pts): pts.append(p)
    return pts, q, rr

random.seed(1)
count = 0
for n in range(3, 7):
    for trial in range(60):
        v = random.randrange(n)
        rest = [k for k in range(n) if k != v]; random.shuffle(rest); pi = rest
        M = {i for i in range(2, n) if random.random() < 0.5}
        V = B_vertices(n, v, pi, M)
        Z, q, rr = zono_vertices(n, v, pi, M)
        assert len(V) == 2 ** (n - 2), (n, len(V))
        assert all(any(np.allclose(p, w) for w in Z) for p in V)
        assert all(any(np.allclose(p, w) for w in V) for p in Z)
        for _ in range(20):
            y = np.random.randn(n)
            h = max([y[v]] + [p @ y for p in V])
            P = lambda i: pi[i - 1]
            f = y[v] + relu(y[P(q)] - y[v] + sum(relu(y[P(rr(i))] - y[P(i)]) for i in range(2, n)))
            assert abs(h - f) < 1e-9
            if M:
                # paper word: perm(0)=v, perm(j+1)=pi_{j+1} (0-based j), S = M-1
                perm = [v] + pi; r = n - 2; S = {i - 1 for i in M}
                qq = max(S); par = lambda j: max({0} | {i for i in S if i < j})
                U = relu(y[perm[qq + 1]] - y[perm[0]] + sum(relu(y[perm[par(j) + 1]] - y[perm[j + 1]]) for j in range(1, r + 1)))
                assert abs(h - (y[v] + U)) < 1e-9
            else:
                c = pi[0]
                star = relu(y[c] - y[v] + sum(relu(y[c] - y[l]) for l in range(n) if l not in (v, c)))
                assert abs(h - (y[v] + star)) < 1e-9
            count += 1
print('all', count, 'checks passed')
