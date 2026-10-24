import json, sys
from inspect_flat import analyse
N, m = int(sys.argv[1]), int(sys.argv[2])
tops = json.load(open(f"flats_{N}_{m}_top.json"))
best = 0
for S in tops:
    S = [(tuple(T), tuple(r)) for T, r in S]
    for s in range(4):
        th, van, good = analyse(N, m, S, seed=s, show=False)
        best = max(best, len(good))
    print(len(S), "best good", max(len(analyse(N, m, S, seed=s, show=False)[2]) for s in range(4)))
print("max good among top flats", best)
