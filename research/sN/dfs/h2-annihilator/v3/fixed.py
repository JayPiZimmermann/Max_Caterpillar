"""H-invariant parts (H = Young subgroup S_mu) of V^TI_N, P_N, Lambda2_N and
Lambda_rays.  usage: fixed.py N mu [rays=all|none|<classfile>]  e.g. fixed.py 5 3,1,1

Braid cells are a free S_N-orbit and gap coordinates are transported
identically by sigma, so an H-invariant f in P_N = data on H-orbit
representatives of cells.  Units are symmetrised on the fly (sum over orbit).
Lambda2 rows are generated combinatorially: for each braid wall (c, c2) on
x_p = x_q and each kink hyperplane a crossing the open wall facet whose pencil
{b in K_N : b restricted to x_p=x_q parallel to a restricted} is exactly
{a, s_pq a} with s_pq a != a: kink coefficient of a equal on both sides.
Ray conditions: exact integer left-null of the germ of the FULL V at the ray,
substituted to representatives.  Ranks mod p (one-sided bounds, see README).
"""
import itertools, sys, time, os, pickle
from math import gcd
import flint
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'v2'))
from ambient import units_of, primitive, classify, gap_form, unit_grad
from bends import family, red
from core import braid_forms, P1

def prim_sign(v):
    return primitive(tuple(v))[0]

class Fixed:
    def __init__(self, N, mu, units=None, verbose=True):
        t0 = time.time()
        self.N = N
        self.units = units if units is not None else units_of(N)
        self.K = family(N)
        self.Kset = set(self.K)
        blocks, s = [], 0
        for m in mu:
            blocks.append(list(range(s, s + m))); s += m
        assert s == N
        self.blocks = blocks
        self.perms = list(itertools.permutations(range(N)))
        self.pidx = {p: i for i, p in enumerate(self.perms)}
        lab = [0] * N
        for b, blk in enumerate(blocks):
            for i in blk: lab[i] = b
        # orbit rep of a cell under H: canonical = replace coordinates within each
        # block by their sorted order of appearance
        def rep(pi):
            cnt = [0] * len(blocks); out = []
            for v in pi:
                b = lab[v]; out.append(blocks[b][cnt[b]]); cnt[b] += 1
            return tuple(out)
        self.rep = {pi: rep(pi) for pi in self.perms}
        reps = sorted(set(self.rep.values()))
        self.reps = reps
        self.ridx = {r: i for i, r in enumerate(reps)}
        # kink directions per cell (gap coords) = family hyperplanes crossing it
        self.D = {}
        for r in reps:
            ds = set()
            for a in self.K:
                g = gap_form(a, r)
                if any(v > 0 for v in g) and any(v < 0 for v in g):
                    ds.add(prim_sign(g))
            self.D[r] = sorted(ds)
        self.off = {}
        n = 0
        self.kix = {}
        for r in reps:
            self.off[r] = n
            self.kix[r] = {p: k for k, p in enumerate(self.D[r])}
            n += N - 1 + len(self.D[r])
        self.nvars = n
        if verbose:
            print(f'N={N} mu={mu} reps={len(reps)} nvars={n} {time.time()-t0:.0f}s', flush=True)

    def vl(self, pi, j):
        return self.off[self.rep[pi]] + j

    def vk(self, pi, p):
        r = self.rep[pi]
        return self.off[r] + self.N - 1 + self.kix[r][p]

    def cell_vec(self, pi, kd, lin, out, mult=1):
        for j, x in enumerate(lin):
            if x: k = self.vl(pi, j); out[k] = out.get(k, 0) + mult * x
        for p, x in kd.items():
            k = self.vk(pi, p); out[k] = out.get(k, 0) + mult * x

    # ---- symmetrised generators ----
    def unit_data(self, key, pi):
        pos = {v: r for r, v in enumerate(pi)}
        return classify(gap_form(unit_grad(key, pos), pi))

    def sym_vec(self, f):
        out = {}
        for pi in self.perms:
            kd, lin = f(pi)
            self.cell_vec(pi, kd, lin, out)
        return {k: x for k, x in out.items() if x}

    def V_sym(self):
        N = self.N
        vecs = [self.sym_vec(lambda pi, k=k: self.unit_data(k, pi)) for k in self.units]
        for i in range(N):
            for j in range(N):
                if i != j:
                    a = [0] * N; a[i], a[j] = 1, -1
                    vecs.append(self.sym_vec(lambda pi, a=tuple(a): classify(gap_form(a, pi))))
        for i in range(1, N):
            a = [0] * N; a[i], a[0] = 1, -1
            vecs.append(self.sym_vec(lambda pi, a=tuple(a): ({}, gap_form(a, pi))))
        return [v for v in vecs if v]

    def max_sym(self):
        def f(pi):
            a = [0] * self.N; a[pi[-1]] += 1; a[0] -= 1
            return ({}, gap_form(a, pi))
        return self.sym_vec(f)

    # ---- continuity ----
    def walls(self):
        N = self.N
        for pi in self.perms:
            for j in range(1, N):
                p2 = list(pi); p2[j - 1], p2[j] = p2[j], p2[j - 1]; p2 = tuple(p2)
                if pi < p2:
                    yield pi, p2, j

    def restrict_basis(self, pi, j):
        """(sparse var dict, kinkdict, lin) for the basis functions of cell pi
        restricted to the wall t_j = 0."""
        N = self.N; drop = j - 1; out = []
        for jj in range(N - 1):
            lin = [0] * (N - 1); lin[jj] = 1; del lin[drop]
            out.append((self.vl(pi, jj), {}, tuple(lin)))
        r = self.rep[pi]
        for p in self.D[r]:
            w = list(p); del w[drop]
            kd, lin = classify(tuple(w)) if any(w) else ({}, (0,) * (N - 2))
            out.append((self.vk(pi, p), kd, lin))
        return out

    def continuity(self):
        rows = set()
        for pi, p2, j in self.walls():
            eq = {}
            for sign, cc in ((1, pi), (-1, p2)):
                for var, kd, lin in self.restrict_basis(cc, j):
                    for l, x in enumerate(lin):
                        if x:
                            d = eq.setdefault(('L', l), {}); d[var] = d.get(var, 0) + sign * x
                    for q, x in kd.items():
                        d = eq.setdefault(('K', q), {}); d[var] = d.get(var, 0) + sign * x
            for r in eq.values():
                r = tuple(sorted((k, x) for k, x in r.items() if x))
                if r: rows.add(r)
        return [dict(r) for r in rows]

    def straight_rows(self):
        """(3,1) straightness rows."""
        N = self.N
        pencil_cache = {}
        rows = set()
        for pi, p2, j in self.walls():
            p, q = sorted((pi[j - 1], pi[j]))
            if (p, q) not in pencil_cache:
                d = {}
                for b in self.K:
                    rb = red(b, p, q)
                    if rb is not None: d.setdefault(rb, []).append(b)
                pencil_cache[(p, q)] = d
            pen = pencil_cache[(p, q)]
            for a in self.K:
                g = gap_form(a, pi)
                w = list(g); del w[j - 1]
                if not (any(v > 0 for v in w) and any(v < 0 for v in w)):
                    continue
                sa = list(a); sa[p], sa[q] = sa[q], sa[p]; sa = prim_sign(sa)
                if sa == a: continue
                if set(pen[red(a, p, q)]) != {a, sa}: continue
                ga = prim_sign(g); g2 = prim_sign(gap_form(a, p2))
                r = {}
                k1 = self.vk(pi, ga); k2 = self.vk(p2, g2)
                r[k1] = r.get(k1, 0) + 1; r[k2] = r.get(k2, 0) - 1
                r = tuple(sorted((k, x) for k, x in r.items() if x))
                if r: rows.add(r)
        return [dict(r) for r in rows]

    # ---- ray germs ----
    def adjacent(self, x0):
        vals = sorted(set(x0))
        blocks = [[i for i in range(self.N) if x0[i] == v] for v in vals]
        for combo in itertools.product(*[itertools.permutations(b) for b in blocks]):
            yield tuple(v for blk in combo for v in blk)

    def germ_coords(self, x0, kd_lin_of):
        """germ coordinates of a function given per cell by (kd, lin):
        dict (pi, 'L', j) / (pi, 'K', p) -> value"""
        N = self.N; out = {}
        for pi in self.adjacent(x0):
            kd, lin = kd_lin_of(pi)
            t0 = [x0[pi[j]] - x0[pi[j - 1]] for j in range(1, N)]
            L = list(lin)
            for p, x in kd.items():
                s = sum(a * b for a, b in zip(p, t0))
                if s > 0:
                    for jj in range(N - 1): L[jj] += x * p[jj]
                elif s == 0:
                    out[(pi, 'K', p)] = x
            for jj in range(N - 1):
                if L[jj]: out[(pi, 'L', jj)] = L[jj]
        return out

    def germ_row_vars(self, x0, key):
        """the germ coordinate `key` as a sparse row on the rep variables"""
        pi, typ, z = key
        N = self.N
        if typ == 'K':
            return {self.vk(pi, z): 1}
        t0 = [x0[pi[j]] - x0[pi[j - 1]] for j in range(1, N)]
        r = {self.vl(pi, z): 1}
        for p in self.D[self.rep[pi]]:
            if p[z] and sum(a * b for a, b in zip(p, t0)) > 0:
                k = self.vk(pi, p); r[k] = r.get(k, 0) + p[z]
        return r

    def ray_conditions(self, x0):
        N = self.N
        gens = [lambda pi, k=k: self.unit_data(k, pi) for k in self.units]
        for i in range(N):
            for j in range(N):
                if i != j:
                    a = [0] * N; a[i], a[j] = 1, -1
                    gens.append(lambda pi, a=tuple(a): classify(gap_form(a, pi)))
        for i in range(1, N):
            a = [0] * N; a[i], a[0] = 1, -1
            gens.append(lambda pi, a=tuple(a): ({}, gap_form(a, pi)))
        # all germ coordinate keys
        keys = []
        for pi in self.adjacent(x0):
            for jj in range(N - 1): keys.append((pi, 'L', jj))
            t0 = [x0[pi[j]] - x0[pi[j - 1]] for j in range(1, N)]
            for p in self.D[self.rep[pi]]:
                if sum(a * b for a, b in zip(p, t0)) == 0:
                    keys.append((pi, 'K', p))
        ki = {k: i for i, k in enumerate(keys)}
        cols = set()
        for g in gens:
            gc = self.germ_coords(x0, g)
            col = [0] * len(keys)
            for k, x in gc.items(): col[ki[k]] = x
            if any(col): cols.add(tuple(col))
        cols = sorted(cols)
        if cols:
            M = flint.fmpz_mat(len(cols), len(keys), [x for c in cols for x in c])
            rV = M.rank()
            X, nul = M.nullspace()
        else:
            rV, nul = 0, len(keys)
            X = flint.fmpz_mat(len(keys), len(keys), [int(i == j) for i in range(len(keys)) for j in range(len(keys))])
        krow = [self.germ_row_vars(x0, k) for k in keys]
        conds = []
        for c in range(nul):
            y = [int(X[i, c]) for i in range(len(keys))]
            row = {}
            for yi, r in zip(y, krow):
                if yi:
                    for v, x in r.items(): row[v] = row.get(v, 0) + yi * x
            row = {k: x for k, x in row.items() if x}
            if row: conds.append(row)
        return conds, rV, len(keys)

    def nmod(self, rows, p=P1):
        M = flint.nmod_mat(max(len(rows), 1), self.nvars, p)
        for i, r in enumerate(rows):
            for k, x in r.items(): M[i, k] = x % p
        return M


if __name__ == '__main__':
    N = int(sys.argv[1]); mu = [int(t) for t in sys.argv[2].split(',')]
    mode = sys.argv[3] if len(sys.argv) > 3 else 'none'
    t0 = time.time()
    F = Fixed(N, mu)
    C = F.continuity(); S2 = F.straight_rows()
    rC = F.nmod(C).rank(); r2 = F.nmod(C + S2).rank()
    print(f'dim P^H = {F.nvars - rC}  dim Lambda2^H <= {F.nvars - r2}  (#straight rows {len(S2)}) {time.time()-t0:.0f}s', flush=True)
    V = F.V_sym()
    rV = F.nmod(V).rank()
    m = F.max_sym()
    print(f'dim V^H >= {rV}   max in V^H: {F.nmod(V + [m]).rank() == rV}  {time.time()-t0:.0f}s', flush=True)
    # exact check V^H inside Lambda2 rows
    bad = sum(1 for r in S2 for v in V if sum(x * v.get(k, 0) for k, x in r.items()))
    print('straight rows violated by sym V (exact):', bad, flush=True)
    if mode != 'none':
        from core import all_rays, canon
        if mode == 'all':
            hy = F.K + braid_forms(N)
            R = all_rays(N, hy)
            # H-orbits of rays: canonical under H permutations
            Hperms = [sum((list(pp) for pp in prod), []) for prod in itertools.product(*[itertools.permutations(b) for b in F.blocks])]
            seen = set(); reps = []
            for x in R:
                c = min(tuple(x[s[i]] - x[s[0]] + 0 for i in range(N)) for s in Hperms)
                c = min(tuple(x[s[i]] for i in range(N)) for s in Hperms)
                if c not in seen: seen.add(c); reps.append(x)
        else:
            reps = pickle.load(open(mode, 'rb'))
        acc = C + S2; ra = r2
        for x0 in reps:
            conds, rV0, nk = F.ray_conditions(x0)
            if not conds: continue
            r = F.nmod(acc + conds).rank()
            if r > ra:
                print('ray', x0, 'germ keys', nk, 'rV', rV0, 'gain', r - ra, f'{time.time()-t0:.0f}s', flush=True)
                acc += conds; ra = r
        print(f'dim Lambda_rays^H <= {F.nvars - ra}  vs dim V^H >= {rV}', flush=True)
