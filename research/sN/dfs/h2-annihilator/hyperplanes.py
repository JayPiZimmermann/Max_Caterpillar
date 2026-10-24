"""Global kink hyperplanes (x-coordinates, a.1 = 0, primitive up to sign)."""
from ambient import unit_kink_sets, units_of, primitive


def gap_to_x(p, pi):
    N = len(pi)
    a = [0] * N
    for j in range(1, N):
        a[pi[j]] += p[j - 1]
        a[pi[j - 1]] -= p[j - 1]
    return primitive(tuple(a))[0]


def global_hyperplanes(N, units=None):
    units = units or units_of(N)
    perms, data, D = unit_kink_sets(N, units)
    H = set()
    for pi, ds in zip(perms, D):
        for p in ds:
            H.add(gap_to_x(p, pi))
    braid = set()
    for i in range(N):
        for j in range(i + 1, N):
            a = [0] * N
            a[i], a[j] = 1, -1
            braid.add(primitive(tuple(a))[0])
    return sorted(H), sorted(braid)


if __name__ == '__main__':
    import sys
    N = int(sys.argv[1])
    H, B = global_hyperplanes(N)
    print(N, 'kink hyperplanes', len(H), 'braid', len(B), 'kink∩braid', len(set(H) & set(B)))
    from collections import Counter
    print(Counter(tuple(sorted(map(abs, h))) for h in H))
    if N == 4:
        print(H)
