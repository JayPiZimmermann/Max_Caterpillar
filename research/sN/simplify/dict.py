"""Enumerate distinct normalized face-function descriptions (h, M) for N inputs.
Face function U^tau_{pi,S} = relu(h'(x) + sum_{l in M} relu(l(x))) with
h' = h + sum of linear edges, M = hinge edges; normalized: every hinge
l_ij with i>j reversed (relu(x_i-x_j) = relu(x_j-x_i) + x_i - x_j)."""
import itertools, sys

def keys(N):
    r = N - 2
    out = set()
    for pi in itertools.permutations(range(N)):
        for Sm in range(1, 1 << r):
            S = [j for j in range(1, r + 1) if Sm >> (j - 1) & 1]
            q = max(S)
            def par(j):
                c = [i for i in S if i < j]
                return max(c) if c else 0
            edges = [(pi[par(j) + 1], pi[j + 1]) for j in range(1, r + 1)]
            head = [0] * N
            head[pi[q + 1]] += 1; head[pi[0]] -= 1
            for tau in itertools.product(range(3), repeat=r):
                h = head[:]
                M = []
                for (i, j), t in zip(edges, tau):
                    if t == 1:
                        h[i] += 1; h[j] -= 1
                    elif t == 2:
                        if i > j:
                            h[i] += 1; h[j] -= 1
                            M.append((j, i))
                        else:
                            M.append((i, j))
                out.add((tuple(h), tuple(sorted(M))))
    return out

if __name__ == "__main__":
    for N in range(3, int(sys.argv[1]) + 1):
        print(N, len(keys(N)), flush=True)
