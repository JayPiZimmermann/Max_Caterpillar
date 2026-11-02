"""Independent exact finite checks for the selector probability audit.

This checks only the permutation/selection counts, not the network semantics.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial, floor, log
from pathlib import Path
import json


def falling(n, d):
    out = 1
    for j in range(d):
        out *= n-j
    return out if d <= n else 0


rank_cases = 0
for m in range(4, 9):
    counts = {(d, k): 0 for d in range(2, m-1) for k in range(m+1)}
    for rho in permutations(range(m)):
        h = rho[0]  # human gap 1, the anchor gap
        for d in range(2, m-1):
            # z is human tail position 2, t position 2+d.
            # Its d intervening gaps have zero-based indices 2,...,d+1.
            if h > max(rho[2:d+2]):
                for k in range(h+1):
                    counts[d, k] += 1
    for (d, k), count in counts.items():
        actual = Fraction(count, factorial(m))
        expected = (1-Fraction(falling(k, d+1), falling(m, d+1)))/(d+1)
        assert actual == expected, (m, d, k, actual, expected)
        assert actual >= Fraction(m-k, m*(d+1))
        rank_cases += 1


enlarged_rank_cases = 0
for m in range(3, 9):
    counts = {(d, k): 0 for d in range(2, m) for k in range(m+1)}
    for rho in permutations(range(m)):
        h = rho[0]
        for d in range(2, m):
            # Enlarged event: z may be the first tail label. Its intervening
            # gaps now have zero-based indices 1,...,d, still excluding 0.
            if h > max(rho[1:d+1]):
                for k in range(h+1):
                    counts[d, k] += 1
    for (d, k), count in counts.items():
        actual = Fraction(count, factorial(m))
        expected = (1-Fraction(falling(k, d+1), falling(m, d+1)))/(d+1)
        assert actual == expected, (m, d, k, actual, expected)
        assert actual >= Fraction(m-k, m*(d+1))
        enlarged_rank_cases += 1


enlarged_joint_cases = 0
for m in range(3, 8):
    actual_counts = [0]*(m+1)
    for rho in permutations(range(m)):
        h = rho[0]
        for z in range(m):
            for t in range(z+2, m):
                if h > max(rho[z+1:t+1]):
                    for k in range(h+1):
                        actual_counts[k] += 1
    for k, count in enumerate(actual_counts):
        actual = Fraction(count, factorial(m)*m*(m-1))
        expected = sum(Fraction(m-d, m*(m-1)*(d+1)) *
            (1-Fraction(falling(k, d+1), falling(m, d+1))) for d in range(2, m))
        assert actual == expected, (m, k, actual, expected)
        enlarged_joint_cases += 1


geometry_cases = 0
for m in range(17):
    for bits in range(1 << m):
        gamma = {j for j in range(m) if bits >> j & 1}
        k = len(gamma)
        edges = [j for j in range(m-1) if j in gamma and j+1 in gamma]
        q = sum(j > 0 and j-1 not in gamma and j+1 not in gamma for j in gamma)
        nu = len(edges)
        assert q >= k-1-2*nu
        matching, previous = 0, -2
        for j in edges:
            if j > previous+1:
                matching += 1
                previous = j
        assert 2*matching >= nu
        if k >= 4 and 2*q < k:
            assert 8*nu >= k
            assert 16*matching >= k
        geometry_cases += 1


selection_cases = 0
for n in range(8, 17):
    for r in range(1, n-3):
        p = set(range(4, 4+r))
        actual = sum(0 in s and 1 in s and 2 not in s and 3 not in s and
                     len(set(s) & p) == 1 for s in combinations(range(n), 7))
        expected = r*comb(n-r-4, 4) if n-r-4 >= 4 else 0
        assert actual == expected
        selection_cases += 1


asymptotic = []
alpha = 1/3
delta = 1/256
constant = 210*alpha**2*(1-alpha)**4
for n in [1000, 10000, 100000, 1000000]:
    r, m = floor(alpha*n), n-7
    k = floor(delta*m)
    # The uncorrected sum is m*(H_(m-1)-3/2)-(m-3).
    geometric_sum = m*(sum(1/j for j in range(1, m))-1.5)-(m-3)
    correction, ratio = 0.0, 1.0
    for s in range(1, k+1):
        ratio *= (k-s+1)/(m-s+1)
        if s >= 3:
            correction += (m-s)/s*ratio
    base = (geometric_sum-correction)/((m-1)*(m-2))
    selected = r*comb(n-r-4, 4)/comb(n, 7)
    probability = selected*(r-1)/m*base
    asymptotic.append(dict(n=n, r=r, k=k,
        scaled=probability*n**3/log(n), limiting_constant=constant))

enlarged_asymptotic = []
alpha_enlarged = 1/5
constant_enlarged = 210*alpha_enlarged*(1-alpha_enlarged)**4
for n in [1000, 10000, 100000, 1000000]:
    r, m = floor(alpha_enlarged*n), n-7
    k = floor(delta*m)
    geometric_sum = (m+1)*(sum(1/j for j in range(1, m+1))-1.5)-(m-2)
    correction, ratio = 0.0, 1.0
    for s in range(1, k+1):
        ratio *= (k-s+1)/(m-s+1)
        if s >= 3:
            correction += (m+1-s)/s*ratio
    base = (geometric_sum-correction)/(m*(m-1))
    selected = r*comb(n-r-4, 4)/comb(n, 7)
    probability = selected*base
    enlarged_asymptotic.append(dict(n=n, r=r, k=k,
        scaled=probability*n**3/log(n), limiting_constant=constant_enlarged))

result = dict(status="PASS", rank_cases=rank_cases,
    enlarged_rank_cases=enlarged_rank_cases,
    enlarged_joint_position_rank_cases=enlarged_joint_cases,
    geometry_subsets=geometry_cases, selection_cases=selection_cases,
    asymptotic_float_checks=asymptotic,
    enlarged_asymptotic_float_checks=enlarged_asymptotic,
    scope="Exact finite permutation, selection, and isolated-gap geometry checks; network survival and literal Good are not checked here.")
Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
