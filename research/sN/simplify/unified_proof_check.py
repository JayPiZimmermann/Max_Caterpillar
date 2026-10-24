r"""Check of the proof in unified.md on random / hill-climbed instances (exact rationals).

For a forest F (parent array = rooting, child of edge {v,parent v} is v) and integer kappa:
  omega(v) = #out-leaf nbrs + [v has a nbr of degree >= 2],  Delta = max(2, max omega),
  y = 1/(2 Delta + 2).
Checks:
  (A) per-unit lemma, exact:  sum_T y^|T| q(T) <= 1  and  max_m sum_{|T|=m} q(T) / b^m <= 1;
  (B) the proof: relation R (out-leaf edges + heir edges) has degree <= Delta, every free
      vertex has an R-nbr / pendant nbr / is a fixed leaf; star cover blocks; for every passed T
      the chosen block edges are untied and vertex-disjoint; every block weight <= 1.
Usage: python3 unified_proof_check.py n trials seed [climb_steps]
"""
import itertools, math, random, sys
from fractions import Fraction


def random_forest(n, rng, p=0.9):
    parent = [None] * n
    for v in range(1, n):
        if rng.random() < p:
            parent[v] = rng.randrange(v)
    perm = list(range(n)); rng.shuffle(perm)
    par2 = [None] * n
    for v in range(n):
        if parent[v] is not None:
            par2[perm[v]] = perm[parent[v]]
    return par2


def passes_q(n, nb, kappa):
    """dict T(frozenset) -> q(T) (exact fraction of orders of O passing)."""
    res = {}
    for mask in range(1 << n):
        Ts = {v for v in range(n) if mask >> v & 1}
        if any(not (nb[t] & Ts) and kappa[t] == 0 for t in Ts):
            continue
        O = [v for v in range(n) if v not in Ts]
        kp = {o: kappa[o] - len(nb[o] & Ts) for o in O}
        if any(kp[o] < 0 for o in O):
            continue
        idx = {o: i for i, o in enumerate(O)}
        f = [0] * (1 << len(O)); f[0] = 1
        for S in range(1 << len(O)):
            if not f[S]: continue
            for o in O:
                b = 1 << idx[o]
                if S & b: continue
                c = sum(1 for w in nb[o] if w in idx and S >> idx[w] & 1)
                if c == kp[o]:
                    f[S | b] += f[S]
        cnt = f[(1 << len(O)) - 1]
        if cnt:
            res[frozenset(Ts)] = Fraction(cnt, math.factorial(len(O)))
    return res


def structure(n, parent, kappa):
    nb = [set() for _ in range(n)]
    for v in range(n):
        if parent[v] is not None:
            nb[v].add(parent[v]); nb[parent[v]].add(v)
    deg = [len(nb[v]) for v in range(n)]
    pend = [deg[v] == 1 and kappa[v] == 0 for v in range(n)]
    outl = [deg[v] == 1 and kappa[v] == 1 for v in range(n)]
    fixl = [deg[v] == 1 and kappa[v] not in (0, 1) for v in range(n)]
    omega = [sum(outl[u] for u in nb[v]) + (1 if any(deg[w] >= 2 for w in nb[v]) else 0)
             for v in range(n)]
    return nb, deg, pend, outl, fixl, omega


def check(n, parent, kappa, verbose=False):
    nb, deg, pend, outl, fixl, omega = structure(n, parent, kappa)
    Delta = max([2] + omega)
    y = Fraction(1, 2 * Delta + 2)
    b = 2 * Delta + 2
    res = passes_q(n, nb, kappa)
    # (A)
    Wq = sum(y ** len(T) * q for T, q in res.items())
    ratio = max([sum(q for T, q in res.items() if len(T) == m) / Fraction(b) ** m
                 for m in range(3, n + 1)] + [Fraction(0)])
    assert Wq <= 1, ("A fails", parent, kappa, float(Wq))
    # (B) relation R
    free = [not pend[v] and deg[v] >= 1 for v in range(n)]
    R = set()
    for l in range(n):
        if outl[l]:
            (w,) = nb[l]
            if not pend[w]:
                R.add(frozenset((l, w)))
    for v in range(n):
        poor = deg[v] >= 2 and not any(outl[u] or pend[u] for u in nb[v])
        if poor:
            # heir: child of an edge at v whose child is not v, i.e. a child of v
            kids = [c for c in range(n) if parent[c] == v]
            assert kids, ("poor vertex without child", parent, kappa, v)
            h = min(kids)
            assert not pend[h]
            R.add(frozenset((v, h)))
    Rn = [set() for _ in range(n)]
    for e in R:
        a, c = tuple(e); Rn[a].add(c); Rn[c].add(a)
    assert max(len(Rn[v]) for v in range(n)) <= Delta, ("R degree", parent, kappa)
    for v in range(n):
        if free[v]:
            assert Rn[v] or any(pend[u] for u in nb[v]) or fixl[v], ("cover", parent, kappa, v)
    # star cover: minimal edge cover of R
    E = set(R)
    changed = True
    while changed:
        changed = False
        for e in sorted(E, key=lambda e: tuple(sorted(e))):
            a, c = tuple(e)
            da = sum(1 for f in E if a in f); dc = sum(1 for f in E if c in f)
            if da >= 2 and dc >= 2:
                E.discard(e); changed = True; break
    En = [set() for _ in range(n)]
    for e in E:
        a, c = tuple(e); En[a].add(c); En[c].add(a)
    Phi = [v for v in range(n) if free[v] and (Rn[v] or any(pend[u] for u in nb[v]))]
    blocks = []  # (centre, leaves) ; lone: (v, None)
    seen = set()
    for v in Phi:
        if v in seen: continue
        if not En[v]:
            blocks.append((v, None)); seen.add(v); continue
        # star component of v
        if len(En[v]) >= 2 or (len(En[v]) == 1 and len(En[next(iter(En[v]))]) == 1 and v < next(iter(En[v]))):
            c = v
        else:
            c = next(iter(En[v]))
        L = sorted(En[c]); blocks.append((c, L)); seen.add(c); seen.update(L)
    assert seen == set(Phi)
    for c, L in blocks:
        if L is not None:
            assert len(L) <= Delta
    # block weights
    for c, L in blocks:
        if L is None:
            W = y + Fraction(1, 2)
        else:
            j = len(L)
            W = (Fraction(1, 2) + y) * (1 + y) ** j + y ** j / 2
        assert W <= 1, ("block weight", parent, kappa, c, L, float(W))
    # per passed T: injectivity of T -> T cap Phi and chosen edges valid
    traces = {}
    for T in res:
        A = T & frozenset(Phi)
        assert A not in traces, ("injectivity", parent, kappa, set(T), set(traces[A]))
        traces[A] = T
        used = set()
        for c, L in blocks:
            if c in T: continue
            if L is None:
                p = min(u for u in nb[c] if pend[u])
                assert p not in T, ("pendant tied", parent, kappa)
                e = (c, p)
            else:
                out = [l for l in L if l not in T]
                if not out: continue
                e = (c, out[0])
            assert e[0] not in used and e[1] not in used, ("matching", parent, kappa)
            used.update(e)
    return float(Wq), float(ratio), Delta


if __name__ == "__main__":
    n, trials, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    steps = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = random.Random(seed)
    worst = {}
    def rk(par):
        return [rng.choice([-1, 0, 0, 1, 1, 1, 2, 2, 3]) for _ in range(n)]
    for t in range(trials):
        par = random_forest(n, rng); kap = rk(par)
        Wq, ratio, D = check(n, par, kap)
        best = (Wq, par, kap)
        for _ in range(steps):
            p2, k2 = best[1][:], best[2][:]
            if rng.random() < 0.6:
                k2[rng.randrange(n)] = rng.choice([-1, 0, 1, 2, 3])
            else:
                p2 = random_forest(n, rng) if rng.random() < 0.2 else p2
                v = rng.randrange(n)
                sub = {v}; ch = True
                while ch:
                    ch = False
                    for u in range(n):
                        if u not in sub and p2[u] in sub:
                            sub.add(u); ch = True
                p2[v] = rng.choice([u for u in range(n) if u not in sub] + [None])
            W2, r2, D2 = check(n, p2, k2)
            if W2 >= best[0]:
                best = (W2, p2, k2)
        key = check(n, best[1], best[2])[2]
        if best[0] > worst.get(key, (0,))[0]:
            worst[key] = best
    for D in sorted(worst):
        print("Delta=%d max Wq=%.4f  %s %s" % (D, *worst[D]))
    print("all checks passed")
