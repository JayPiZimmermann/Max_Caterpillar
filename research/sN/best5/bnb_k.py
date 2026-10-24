"""Branch and bound (LP) for the free-remainder model:
    max_5 = R + sum_{k<K} d_k relu(g_k),  R in span{x_i, relu(x_i-x_j)}, sum l_R = 1,
    g_k translation invariant in the same span, d_k = +-1 (positive homogeneity).
On each braid cell C every function is a linear form; F = sum d_k relu(g_k) must equal
x_top - R on C, hence be linear on C.  Per cell, each neuron is '+' (g >= 0 on C), '-' (g <= 0)
or mixed; mixed neurons split into the two sides P, Q of a common hyperplane and must satisfy
sum_P d L = sum_Q d L (= their contribution).  (Exact for <= 2 mixed neurons with d = +-1;
a relaxation for >= 3.)  A node is a partial assignment of options to cells; LP feasibility
(HiGHS) prunes.  MEASURED unless every pruning LP is re-certified exactly (see cert step).
Usage: python bnb_k.py K signs maxdepth   e.g.  python bnb_k.py 2 +- 120"""
import sys, itertools, time
import numpy as np
from scipy.optimize import linprog

N = 5
PAIRS = list(itertools.combinations(range(N), 2))
NF = N + len(PAIRS)  # 15 coefficients per function


def cell_map(perm):
    """5 x 15 matrix: (l,a) -> linear form on the cell perm (perm[0] top)."""
    rank = {v: t for t, v in enumerate(perm)}
    M = np.zeros((N, NF))
    for i in range(N):
        M[i, i] = 1
    for q, (i, j) in enumerate(PAIRS):
        if rank[i] < rank[j]:
            M[i, N + q] += 1; M[j, N + q] -= 1
    return M


def beta_map(perm):
    """4 x 5: linear form coefficients -> partial sums along perm (cell basis)."""
    B = np.zeros((N - 1, N))
    for t in range(N - 1):
        for s in range(t + 1):
            B[t, perm[s]] = 1
    return B


def options(K, d):
    """list of (signs tuple over neurons in {'+','-','P','Q'})"""
    out = []
    for o in itertools.product('+-PQ', repeat=K):
        mixed = [k for k in range(K) if o[k] in 'PQ']
        if len(mixed) == 1:
            continue
        if mixed and o[mixed[0]] != 'P':
            continue  # P/Q swap symmetry
        if mixed and all(o[k] == 'P' for k in mixed) and len(mixed) == 2 and d[mixed[0]] == d[mixed[1]]:
            continue  # d L1 + d L2 = 0 with equal d: L2 = -L1, but then both on side P impossible (opposite signs)
        if len(mixed) == 2 and o[mixed[1]] == 'Q' and d[mixed[0]] == d[mixed[1]]:
            continue  # d L1 = d L2 -> L1 = L2: same side, contradiction
        out.append(o)
    return out


class Problem:
    def __init__(self, K, d):
        self.K, self.d = K, d
        self.nv = NF * (1 + K)
        self.cells = list(itertools.permutations(range(N)))
        self.CM = {p: cell_map(p) for p in self.cells}
        self.BM = {p: beta_map(p) for p in self.cells}
        self.opts = options(K, d)
        self.lp = 0

    def block(self, f):
        Z = np.zeros((NF, self.nv)); Z[:, NF * f:NF * (f + 1)] = np.eye(NF); return Z

    def cons(self, perm, o):
        """returns (Aeq, beq, Aub, bub) for option o on cell perm"""
        K, d = self.K, self.d
        C = self.CM[perm]; B = self.BM[perm]
        L = [C @ self.block(1 + k) for k in range(K)]  # 5 x nv
        Rf = C @ self.block(0)
        F = Rf.copy()
        Aeq, beq, Aub, bub = [], [], [], []
        P = [k for k in range(K) if o[k] == 'P']; Q = [k for k in range(K) if o[k] == 'Q']
        for k in range(K):
            if o[k] == '+':
                F = F + d[k] * L[k]; Aub.append(-(B @ L[k]))
            elif o[k] == '-':
                Aub.append(B @ L[k])
        if P or Q:
            SP = sum(d[k] * L[k] for k in P) if P else 0 * Rf
            SQ = sum(d[k] * L[k] for k in Q) if Q else 0 * Rf
            Aeq.append(SP - SQ); beq.append(np.zeros(N))
            F = F + SP
        e = np.zeros(N); e[perm[0]] = 1
        Aeq.append(F); beq.append(e)
        return Aeq, beq, Aub, bub

    def base(self):
        Aeq = []; beq = []
        r = np.zeros(self.nv); r[:N] = 1; Aeq.append(r[None]); beq.append(np.array([1.]))
        for k in range(self.K):
            r = np.zeros(self.nv); r[NF * (1 + k):NF * (1 + k) + N] = 1; Aeq.append(r[None]); beq.append(np.zeros(1))
        return Aeq, beq, [], []

    def feasible(self, parts):
        Aeq = np.vstack([a for p in parts for a in p[0]]); beq = np.concatenate([b for p in parts for b in p[1]])
        ub = [a for p in parts for a in p[2]]
        Aub = np.vstack(ub) if ub else None; bub = np.zeros(Aub.shape[0]) if ub else None
        self.lp += 1
        r = linprog(np.zeros(self.nv), A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(None, None)] * self.nv,
                    method='highs')
        return r.status == 0


def order_cells(cells):
    """BFS order over adjacent transpositions from the identity cell."""
    seen = [cells[0]]; S = {cells[0]}; i = 0
    while i < len(seen):
        p = seen[i]; i += 1
        for t in range(N - 1):
            q = list(p); q[t], q[t + 1] = q[t + 1], q[t]; q = tuple(q)
            if q not in S:
                S.add(q); seen.append(q)
    return seen


def search(K, d, maxdepth, tmax=3600):
    pr = Problem(K, d)
    order = order_cells(pr.cells)[:maxdepth]
    t0 = time.time(); nodes = [0] * (len(order) + 1); sols = []
    base = pr.base()

    def rec(i, parts):
        nodes[i] += 1
        if time.time() - t0 > tmax:
            raise TimeoutError
        if i == len(order):
            sols.append(list(parts)); return
        for o in pr.opts:
            c = pr.cons(order[i], o)
            if pr.feasible(parts + [c]):
                rec(i + 1, parts + [c])
    try:
        rec(0, [base])
        status = 'complete'
    except TimeoutError:
        status = 'timeout'
    return status, nodes, len(sols), pr.lp, time.time() - t0


if __name__ == '__main__':
    K = int(sys.argv[1]); d = [1 if c == '+' else -1 for c in sys.argv[2]]
    md = int(sys.argv[3]); tmax = float(sys.argv[4]) if len(sys.argv) > 4 else 3600
    st, nodes, ns, lp, dt = search(K, d, md, tmax)
    print('K', K, 'd', d, 'depth', md, status := st, 'nodes per depth', nodes, 'leaves feasible', ns, 'LPs', lp, '%.0fs' % dt)
