"""Membership of max_N in span(family of general neurons) + A, measured by rank mod p
on random integer points (rank is a certified lower bound for the sampled matrix; the
membership verdict 'True' is a lead until certified on cells).

Families (g written as integer combos of 'pair maxima' m_P, |P|<=2, m_{i}=x_i,
m_{ij}=x_j+relu(x_i-x_j)):
  F1: g = m_P - m_Q            (P != Q)
  F2: g = m_P + m_Q - m_R - m_S
  F3: g = m_P + m_Q - m_R - m_S - m_U + m_V? (not used)
Usage: python family_span.py N fam
"""
import sys, itertools
import numpy as np
from gn import feats, pairs, sample, rank_np_mod_p, P


def mvec(N, S):
    """weight vector over feats [x_i, relu(x_i-x_j) i<j] of m_S."""
    pr = pairs(N)
    w = np.zeros(N + len(pr), dtype=np.int64)
    S = sorted(S)
    if len(S) == 1:
        w[S[0]] = 1
    else:
        i, j = S
        w[j] = 1
        w[N + pr.index((i, j))] = 1
    return w


def family(N, fam):
    subs = [(i,) for i in range(N)] + list(itertools.combinations(range(N), 2))
    M = {S: mvec(N, S) for S in subs}
    out = {}
    if fam == 'F1':
        for S, T in itertools.permutations(subs, 2):
            w = M[S] - M[T]
            out[w.tobytes()] = w
    elif fam == 'F2':
        for S, T in itertools.combinations_with_replacement(subs, 2):
            for R, U in itertools.combinations_with_replacement(subs, 2):
                if {S, T} & {R, U}:
                    continue
                w = M[S] + M[T] - M[R] - M[U]
                out[w.tobytes()] = w
    return np.array(list(out.values()))


if __name__ == '__main__':
    N = int(sys.argv[1]); fam = sys.argv[2]
    W = family(N, fam)
    print('N', N, fam, 'neurons', len(W), flush=True)
    m = len(W) + 200
    X = sample(N, m, 7)
    F = feats(X)
    G = np.maximum(F @ W.T, 0)
    M0 = np.concatenate([G, F], 1)
    r0 = rank_np_mod_p(M0)
    r1 = rank_np_mod_p(np.concatenate([M0, X.max(1)[:, None]], 1))
    print('rank', r0, 'with max', r1, 'max in span:', r0 == r1, flush=True)
    np.save('fam_%s_N%d.npy' % (fam, N), W)
