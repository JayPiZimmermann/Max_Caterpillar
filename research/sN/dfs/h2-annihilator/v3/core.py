"""Core objects for the annihilator of V^TI_N inside the ambient P_N.

P_N: continuous translation-invariant positively homogeneous functions that on
every open braid cell are linear + sum_{H in K_N crossing the cell} c_H relu(H)
(K_N = kink family, see ../v2/bends.family; equals the unit kink hyperplanes for
N <= 6, checked by crossing.py / v2/hyp6.py).  Coordinates: per cell pi, the
N-1 gap-linear coefficients and one coefficient per crossing kink direction
(ambient.Ambient).  V^TI_N = span(units, relu(x_i-x_j), TI linear).

Everything integer; ranks mod a prime are used only as one-sided bounds
(rank_p <= rank_Q).
"""
import itertools, os, sys, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'v2'))
from ambient import Ambient, unit_kink_sets, units_of, cell_data, base_funcs, classify, gap_form
from bends import family
from germs2 import rays as all_rays, canon
import flint

P1 = 2_147_483_629
P2 = 2_147_483_587


def braid_forms(N):
    out = []
    for i in range(N):
        for j in range(i + 1, N):
            a = [0] * N; a[i], a[j] = 1, -1
            out.append(tuple(a))
    return out


class Setup:
    def __init__(self, N, units=None):
        self.N = N
        self.units = units if units is not None else units_of(N)
        perms, data, D = unit_kink_sets(N, self.units)
        self.perms = perms
        self.A = Ambient(N, D)
        self.C = self.A.constraints()
        _, bdata = cell_data(N, base_funcs(N))
        self.unit_vecs = [self.A.vector(r) for r in data]
        self.base_vecs = [self.A.vector(r) for r in bdata]
        self.V = self.unit_vecs + self.base_vecs
        self.K = family(N)
        self.hyps = self.K + braid_forms(N)

    def nmod(self, rows, p=P1, ncols=None):
        ncols = ncols or self.A.nvars
        M = flint.nmod_mat(len(rows), ncols, p)
        for i, r in enumerate(rows):
            for k, x in r.items():
                M[i, k] = x % p
        return M

    # ---- germ at a point x0 (integer vector) -------------------------------
    def adjacent_cells(self, x0):
        N = self.N
        vals = sorted(set(x0))
        blocks = [[i for i in range(N) if x0[i] == v] for v in vals]
        for combo in itertools.product(*[itertools.permutations(b) for b in blocks]):
            pi = tuple(v for blk in combo for v in blk)
            yield self.A.pidx[pi], pi

    def germ_rows(self, x0):
        """Integer sparse rows (dict var->coef) whose joint kernel on P_N is
        exactly the set of f with zero germ at x0."""
        N, A = self.N, self.A
        rows = []
        for c, pi in self.adjacent_cells(x0):
            t0 = [x0[pi[j]] - x0[pi[j - 1]] for j in range(1, N)]
            active = []
            through = []
            for p in A.D[c]:
                s = sum(a * b for a, b in zip(p, t0))
                if s > 0:
                    active.append(p)
                elif s == 0:
                    through.append(p)
            for j in range(N - 1):
                r = {A.var_lin(c, j): 1}
                for p in active:
                    if p[j]:
                        r[A.var_kink(c, p)] = p[j]
                rows.append(r)
            for p in through:
                rows.append({A.var_kink(c, p): 1})
        return rows


def apply_rows(rows, vecs):
    """Integer matrix rows x vecs: entry = row . vec."""
    return [[sum(x * v.get(k, 0) for k, x in r.items()) for v in vecs] for r in rows]
