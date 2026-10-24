import itertools, sys
from fractions import Fraction as Fr
m = int(sys.argv[1]); D = int(sys.argv[2])
grid = [Fr(k, D) for k in range(-m * D, 1)]
thetas = [th for k in range(m + 1) for th in itertools.combinations(range(m), k)]
C = [[sum(1 for j in th if j >= i) for i in range(m)] for th in thetas]
cnt = 0
for G in itertools.product(grid, repeat=m):
    ok = True; val = [Fr(0)] * m
    for th, c in zip(thetas, C):
        R = [G[i] + c[i] for i in range(m)]
        pos = any(r > 0 for r in R); neg = any(r < 0 for r in R)
        if pos and neg: ok = False; break
        if pos:
            for i in range(m): val[i] += (-1) ** len(th) * R[i]
    if ok and any(val):
        cnt += 1
        if cnt <= 40: print('Gamma', [str(g) for g in G], 'value', [str(v) for v in val])
print('m', m, 'D', D, 'solutions', cnt)
