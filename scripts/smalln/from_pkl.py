#!/usr/bin/env python3
"""Convert an h5-growth pickle {'N', 'd': {(h, M): coef}} into the JSON input
format of gen_lean.py (see README.md).

The auxiliary coefficients are not stored in the pickles.  They are recomputed
with scripts/vocabulary_search.exact_expansion, which solves
max_N = sum_k d_k U_k + sum_a e_a aux_a over Q on the given support and
verifies the relation exactly on every cell of the braid-and-zero arrangement.
The script refuses inputs whose support carries no exact expansion, and checks
that the recomputed unit coefficients equal the stored ones.

usage: python3 scripts/smalln/from_pkl.py data.pkl Name out.json [source note]
"""
import json
import os
import pickle
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import vocabulary_search as vs  # noqa: E402


def dumps(js):
    """JSON with one unit / auxiliary term per line."""
    head = {k: v for k, v in js.items() if k not in ('units', 'aux')}
    lines = ['{'] + [f' {json.dumps(k)}: {json.dumps(v)},' for k, v in head.items()]
    lines.append(' "units": [')
    lines.append(',\n'.join('  ' + json.dumps(u) for u in js['units']))
    lines.append(' ],')
    lines.append(' "aux": [')
    lines.append(',\n'.join('  ' + json.dumps(a) for a in js['aux']))
    lines.append(' ]')
    lines.append('}')
    return '\n'.join(lines) + '\n'


def main():
    src, name, out = sys.argv[1], sys.argv[2], sys.argv[3]
    note = sys.argv[4] if len(sys.argv) > 4 else src
    data = pickle.load(open(src, 'rb'))
    N = data['N']
    units = sorted(data['d'])
    res = vs.exact_expansion(N, units)
    if res is None:
        sys.exit(f'{src}: no exact expansion of max_{N} on this support '
                 '(e.g. a "top"-mode solution that only matches the top Moebius row)')
    d, e = res
    for k in units:
        if Fraction(data['d'][k]) != d[k]:
            sys.exit(f'{src}: stored coefficient of {k} differs from the exact solve')
    # sigma(x_i) and sigma(-x_i) with opposite coefficients are the coordinate x_i
    aux = []
    for i in range(N):
        p, q = e.get(('pos', i), Fraction(0)), e.get(('neg', i), Fraction(0))
        if p + q != 0:
            aux.append({'coef': str(p + q), 'kind': 'pos', 'i': i})
        if q != 0:
            aux.append({'coef': str(-q), 'kind': 'lin', 'i': i})
    for a, c in e.items():
        if a[0] == 'pair' and c != 0:
            aux.append({'coef': str(c), 'kind': 'pair', 'i': a[1], 'j': a[2]})
    js = {
        'name': name,
        'N': N,
        'source': note,
        'units': [{'coef': str(d[k]), 'head': list(k[0]), 'pairs': sorted(list(p) for p in k[1])}
                  for k in units if d[k] != 0],
        'aux': aux,
    }
    with open(out, 'w') as f:
        f.write(dumps(js))
    print(f'{out}: N={N}, {len(js["units"])} units, {len(aux)} auxiliary terms')


if __name__ == '__main__':
    main()
