"""Check whether caterpillar units U_k = relu(A_k) are chamber-compatible:
A_k (translation invariant, linear on Weyl chambers) has constant sign on every
chamber, i.e. no S subset T with f(S) f(T) < 0, where f(S) = A_k(1_S)."""
import sys, itertools
sys.path.insert(0, '/home/jzimmermann/code/Max_Caterpillar/scripts')
from vocabulary_search import dictionary

def f_of(key, N):
    h, M = key
    f = {}
    for mask in range(1 << N):
        s = [(mask >> i) & 1 for i in range(N)]
        f[mask] = sum(h[i] * s[i] for i in range(N)) + sum(max(s[i] - s[j], 0) for i, j in M)
    return f

def compatible(f, N):
    full = (1 << N) - 1
    for S in range(1 << N):
        if f[S] == 0: continue
        # supersets
        T = S
        rest = full & ~S
        sub = rest
        while True:
            if f[S | sub] * f[S] < 0:
                return False
            if sub == 0: break
            sub = (sub - 1) & rest
    return True

for N in range(3, int(sys.argv[1]) + 1):
    K0, full = dictionary(N)
    bad = [k for k in K0 if not compatible(f_of(k, N), N)]
    print(N, len(K0), 'incompatible:', len(bad))
