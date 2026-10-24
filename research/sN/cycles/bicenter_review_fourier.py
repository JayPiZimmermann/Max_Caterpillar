#!/usr/bin/env python3
"""Independent conditional-leaf Fourier calculation for bicentre graphs.

The common Fourier factor i**(-n) is omitted. Generic rational frequencies
sum to zero. This is research code, not a Lean certificate.
"""
import argparse
import itertools
import json
import random
from fractions import Fraction as Q


def full_value(h, edges, apex, c, d, om):
    """Full K_{2,n-3}, optionally with centre edge, in O(2**(n-3))."""
    n = len(h)
    leaves = [v for v in range(n) if v not in (apex, c, d)]
    expected = {frozenset((v, w)) for v in leaves for w in (c, d)}
    actual = {frozenset(e) for e in edges}
    assert actual in (expected, expected | {frozenset((c, d))})
    assert len(actual) == len(edges)
    assert h[apex] == -1 and sum(h) == 0 and sum(om) == 0
    kappa = list(h)
    for u, v in edges:
        kappa[u] += 1
    a = om[apex]
    B = [om[v] + a * (kappa[v] - 1) for v in leaves]
    D0, D1 = om[d] + a * kappa[d], -om[c] - a * kappa[c]
    out = Q(0)
    for mask in range(1 << len(leaves)):
        den, s = 1, 0
        for j, b in enumerate(B):
            selected = (mask >> j) & 1
            den *= b * (b + a if selected else b - a)
            if selected:
                s += b
        out += (Q(1, D0 + s) - Q(1, D1 - s)) / den
    return Q((-a) ** len(leaves), a * a) * out


def subgraph_value(h, edges, apex, c, d, om):
    """Any subgraph and general head; linear edge states are absorbed in h."""
    n = len(h)
    leaves = [v for v in range(n) if v not in (apex, c, d)]
    allowed = {frozenset((v, w)) for v in leaves for w in (c, d)}
    allowed.add(frozenset((c, d)))
    assert len(edges) == len({frozenset(e) for e in edges})
    assert all(frozenset(e) in allowed for e in edges)
    assert h[apex] == -1 and sum(h) == 0 and sum(om) == 0
    edges = set(edges)
    a = om[apex]
    out = Q(0)
    for positive in (True, False):
        choices = []
        for v in leaves:
            Ic = int((v, c) in edges or (c, v) in edges)
            Id = int((v, d) in edges or (d, v) in edges)
            if Ic == 0 and Id == 0:
                return Q(0)
            p, q = int((v, c) in edges), int((v, d) in edges)
            omega = om[v] + a * h[v]
            A0 = omega - a * (Ic * (1 - p) + Id * (1 - q))
            options = []
            if positive:
                if Ic:
                    options.append((Q(1, A0 + a * Ic) - Q(1, A0),
                                    a * Id * (1 - q)))
                if Id:
                    options.append((Q(1, A0 + a * (Ic + Id)) - Q(1, A0 + a * Ic),
                                    omega + a * Ic * p))
            else:
                if Id:
                    options.append((Q(1, A0 + a * Id) - Q(1, A0),
                                    omega - a * Ic * (1 - p)))
                if Ic:
                    options.append((Q(1, A0 + a * (Ic + Id)) - Q(1, A0 + a * Id),
                                    -a * Id * q))
            choices.append(options)
        centre_frequency = om[d] + a * h[d]
        if positive and (d, c) in edges:
            centre_frequency += a
        if not positive and (c, d) in edges:
            centre_frequency -= a
        for terms in itertools.product(*choices):
            coefficient, frequency = Q(1), centre_frequency
            for coef, freq in terms:
                coefficient *= coef
                frequency += freq
            out += (1 if positive else -1) * coefficient / frequency
    return out / (a * a)


def full_mod_batch(kappa, apex, c, d, frequencies, inverse, prime):
    """Full-graph formula on an M-by-n integer NumPy frequency array.

    `inverse` is the modular inverse lookup table, inverse[0] = 0.
    The caller supplies kappa = h + outdegree. Requires prime**2 < 2**63.
    A singular input raises; do not silently treat it as a zero sample.
    """
    import numpy as np
    assert prime * prime < 2 ** 63
    frequencies = np.asarray(frequencies, dtype=np.int64)
    n = frequencies.shape[1]
    leaves = [v for v in range(n) if v not in (apex, c, d)]
    a = frequencies[:, apex] % prime
    B = [(frequencies[:, v] + a * (kappa[v] - 1)) % prime for v in leaves]
    D0 = (frequencies[:, d] + a * kappa[d]) % prime
    D1 = (-frequencies[:, c] - a * kappa[c]) % prime
    out = np.zeros(len(a), dtype=np.int64)
    if np.any(a == 0):
        raise ZeroDivisionError("apex frequency")
    for mask in range(1 << len(leaves)):
        den, s = np.ones(len(a), dtype=np.int64), np.zeros(len(a), dtype=np.int64)
        for j, b in enumerate(B):
            selected = (mask >> j) & 1
            den = den * b % prime
            den = den * ((b + a if selected else b - a) % prime) % prime
            if selected:
                s = (s + b) % prime
        dp, dm = (D0 + s) % prime, (D1 - s) % prime
        if np.any(den == 0) or np.any(dp == 0) or np.any(dm == 0):
            raise ZeroDivisionError("conditional partial-fraction pole")
        out = (out + ((inverse[dp] - inverse[dm]) % prime) * inverse[den]) % prime
    prefactor = inverse[a] * inverse[a] % prime
    for _ in leaves:
        prefactor = prefactor * (-a % prime) % prime
    return prefactor * out % prime


def control():
    from cycle_fourier import chamber_value
    rng = random.Random(241024137)
    records = []
    for n in (4, 5, 6):
        apex, c, d = n - 1, 0, 1
        underlying = [(v, w) for v in range(2, n - 1) for w in (c, d)]
        underlying.append((c, d))
        for case in range(12):
            h = [0] * n
            h[case % (n - 1)], h[apex] = 1, -1
            edges = []
            full = case < 6
            for u, v in underlying:
                state = rng.randrange(2) + 3 if full else rng.randrange(5)
                if full and (u, v) == (c, d) and case % 2:
                    state = 0
                if state in (1, 2):
                    s = 1 if state == 1 else -1
                    h[u] += s
                    h[v] -= s
                elif state == 3:
                    edges.append((u, v))
                elif state == 4:
                    edges.append((v, u))
            # Also test general heads, independently of the face-state generator.
            if case % 3 == 2:
                h[c] += 2
                h[d] -= 2
            for attempt in range(100):
                om = [rng.randrange(1, 100000) for _ in range(n - 1)]
                om.append(-sum(om))
                rng.shuffle(om)
                try:
                    got = subgraph_value(h, edges, apex, c, d, om)
                    expected = chamber_value((h, edges), om)
                    if full:
                        short = full_value(h, edges, apex, c, d, om)
                    break
                except ZeroDivisionError:
                    continue
            else:
                raise RuntimeError("No nonsingular control frequency found")
            assert got == expected, (n, case, got, expected, h, edges, om)
            if full:
                assert short == expected, (n, case, short, expected)
            records.append(dict(n=n, case=case, full=full, nonzero=bool(got)))
    print(json.dumps(dict(status="exact-control-pass", records=records), indent=2))


def control_mod():
    import numpy as np
    prime = 1000003
    inverse = np.zeros(prime, dtype=np.int64)
    inverse[1] = 1
    for k in range(2, prime):
        inverse[k] = prime - (prime // k) * inverse[prime % k] % prime
    rng = random.Random(1772)
    count, singular_batches = 0, 0
    for n in (4, 5, 6, 7):
        apex, c, d = n - 1, 0, 1
        for case in range(5):
            edges = [(v, w) if rng.randrange(2) else (w, v)
                     for v in range(2, n - 1) for w in (c, d)]
            if case % 3:
                edges.append((c, d) if case % 3 == 1 else (d, c))
            h = [0] * n
            h[case % (n - 1)], h[apex] = 1, -1
            kappa = h.copy()
            for u, v in edges:
                kappa[u] += 1
            frequencies = []
            for _ in range(10):
                om = [rng.randrange(1, 1000) for _ in range(n - 1)]
                om.append(-sum(om))
                rng.shuffle(om)
                frequencies.append(om)
            try:
                got = full_mod_batch(kappa, apex, c, d, frequencies, inverse, prime)
            except ZeroDivisionError:
                singular_batches += 1
                continue
            for om, value in zip(frequencies, got):
                rational = full_value(h, edges, apex, c, d, om)
                assert rational.numerator * pow(rational.denominator, -1, prime) % prime == value
                count += 1
    print(json.dumps(dict(status="exact-batch-control-pass", checks=count,
                          rejected_singular_batches=singular_batches), indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["control", "control-mod"])
    args = parser.parse_args()
    if args.command == "control":
        control()
    else:
        control_mod()
