"""Same as rank.py but evaluates at all primitive integer points of the box
[-R,R]^{N-1} (x_0 = 0), which hits every cone of a fan with small integer
data once R is large enough."""
import numpy as np, sys, time, itertools, math
from dict import keys
from rank import rank_mod, evalF, evalA0

def grid(N, R):
    pts = []
    for v in itertools.product(range(-R, R + 1), repeat=N - 1):
        g = 0
        for a in v: g = math.gcd(g, a)
        if g == 1: pts.append((0,) + v)
    return np.array(pts, dtype=np.int64)

if __name__ == "__main__":
    N = int(sys.argv[1]); R = int(sys.argv[2])
    t = time.time()
    X = grid(N, R)
    ks = sorted(keys(N))
    A = evalA0(N, X); F = evalF(ks, X)
    ra = rank_mod(A.T.copy()); rf = rank_mod(np.vstack([A, F]).T.copy())
    print(N, R, len(X), (ra, rf, rf - ra, len(ks)), round(time.time() - t, 1), flush=True)
