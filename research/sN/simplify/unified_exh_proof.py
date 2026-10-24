"""Exhaustive run of unified_proof_check.check over all forests on n vertices (up to
isomorphism, every rooting choice = BFS from the least vertex of each component) and all
kappa in {-1, ..., deg+1}.  Usage: python3 unified_exh_proof.py forests_n.txt n"""
import itertools, sys
from unified_proof_check import check
path, n = sys.argv[1], int(sys.argv[2])
cnt = 0; worst = 0.0
for line in open(path):
    a = list(map(int, line.split())); ne = a[0]; E = [(a[1 + 2 * i], a[2 + 2 * i]) for i in range(ne)]
    nb = [set() for _ in range(n)]
    for u, v in E: nb[u].add(v); nb[v].add(u)
    for root_choice in range(n):          # several rootings
        parent = [None] * n; seen = set()
        order = [root_choice] + [v for v in range(n) if v != root_choice]
        for r in order:
            if r in seen: continue
            seen.add(r); q = [r]
            while q:
                x = q.pop()
                for y in nb[x]:
                    if y not in seen: seen.add(y); parent[y] = x; q.append(y)
        for kap in itertools.product(*[range(-1, len(nb[v]) + 2) for v in range(n)]):
            Wq, ratio, D = check(n, parent, list(kap)); cnt += 1; worst = max(worst, ratio)
print("n=%d instances %d (forests x rootings x kappa): all proof checks passed; max_m ratio %.4f" % (n, cnt, worst))
