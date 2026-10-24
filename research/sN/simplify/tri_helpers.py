import itertools
def lamT(N, T, rho, f):
    z = [0] * N
    for j, l in enumerate(rho): z[l] = 4 * (j + 1)
    for t in T: z[t] = 4 * (N - 2)
    tot = 0
    for e in itertools.product((0, 1), repeat=3):
        x = z[:]
        for t, ei in zip(T, e): x[t] += ei
        tot += (-1) ** sum(e) * f(x)
    return tot

