# Independent check (direct evaluation of the full neuron, exact integers):
# count localities rho (T = top m labels, others at -B^e) at which the m-th
# mixed difference Delta_rho U != 0, for
#   signed star : U = relu( sum_{p in P} relu(x_p-x_0) - sum_{q in Q} relu(x_q-x_0) )
#   convex star : U = relu( -2(x_f-x_s) + relu(x_f-x_s) + sum_{l in L} relu(x_l-x_s) )
# Uses the paper's base point p_o = 0 (tied) / -B^{pos} and cube side delta=1
# (B = 10*N so that delta < 1 is not needed: all functions are homogeneous
#  and the outside gaps exceed the cube side by a factor B).
import itertools, sys
from math import comb, factorial
relu = lambda t: t if t > 0 else 0
def count(N, m, U, B=None):
    B = B or 10*N
    seen = 0; tot = 0
    for T in itertools.combinations(range(N), m):
        O = [o for o in range(N) if o not in T]
        for ordO in itertools.permutations(O):
            tot += 1
            base = [0]*N
            for pos, o in enumerate(ordO):
                base[o] = -B**(pos+1)
            lam = 0
            for r in range(m+1):
                for S in itertools.combinations(T, r):
                    x = base[:]
                    for t in S: x[t] += 1
                    lam += (-1)**(m-r) * U(x)
            if lam != 0: seen += 1
    return seen, tot
def signed_star(N):
    P = list(range(1, 1+(N-1)//2)); Q = list(range(1+(N-1)//2, N))
    return lambda x: relu(sum(relu(x[p]-x[0]) for p in P) - sum(relu(x[q]-x[0]) for q in Q)), P, Q
def convex_star(N):
    s, f = 0, 1; L = range(2, N)
    return lambda x: relu(-2*(x[f]-x[s]) + relu(x[f]-x[s]) + sum(relu(x[l]-x[s]) for l in L))
for N in range(4, 8):
    U, P, Q = signed_star(N)
    for m in range(3, N+1):
        s, t = count(N, m, U)
        pred = (comb(N-1, m-1) - comb(len(P), m-1) - comb(len(Q), m-1)) * factorial(N-m)
        s2, _ = count(N, m, convex_star(N))
        pred2 = comb(N-2, m-2) * factorial(N-m)
        print(f"N={N} m={m} localities={t} signed_star_seen={s} (pred {pred}) convex_star_seen={s2} (pred {pred2})")
        sys.stdout.flush()
