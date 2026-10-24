"""Emit all forests on n vertices up to isomorphism as edge lists (one per line)."""
import itertools, sys
n = int(sys.argv[1])
seen = set(); out = []
for par in itertools.product(*[[None] + list(range(v)) for v in range(n)]):
    E = [(par[v], v) for v in range(n) if par[v] is not None]
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in E))
        if best is None or key < best: best = key
    if best not in seen:
        seen.add(best); out.append(best)
for E in out:
    print(len(E), " ".join("%d %d" % e for e in E))
print("#", len(out), file=sys.stderr)
