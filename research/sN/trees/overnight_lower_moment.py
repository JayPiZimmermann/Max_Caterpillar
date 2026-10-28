#!/usr/bin/env python3
"""Bounded exploration of symmetric coordinate-curvature moments.

This is only an instrument: no annihilation of L_k is assumed. All values
are exact Fractions. A failed star control rejects a candidate functional.
"""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path


def coefficients(n, root, edges, j, x, sample):
    a = Q((root == j) - (j == 0))
    b = Q((x[root] if root != j else 0) - (x[0] if j != 0 else 0))
    for u, v in edges:
        c = (u == j) - (v == j)
        d = (x[u] if u != j else 0) - (x[v] if v != j else 0)
        if c * sample + d > 0:
            a += c
            b += d
    return a, b


def moment(n, root, edges, j, x, order):
    cuts = sorted({Q(x[v if u == j else u]) for u, v in edges if j in (u, v)})
    ends = [None] + cuts + [None]
    roots = set(cuts)
    for lo, hi in zip(ends, ends[1:]):
        t = (lo + hi) / 2 if lo is not None and hi is not None else (hi-1 if hi is not None else (lo+1 if lo is not None else Q(0)))
        a, b = coefficients(n, root, edges, j, x, t)
        if a:
            z = -b/a
            if (lo is None or lo < z) and (hi is None or z < hi):
                roots.add(z)
    cuts = sorted(roots)
    ends = [None] + cuts + [None]
    slopes = []
    for lo, hi in zip(ends, ends[1:]):
        t = (lo + hi) / 2 if lo is not None and hi is not None else (hi-1 if hi is not None else (lo+1 if lo is not None else Q(0)))
        a, b = coefficients(n, root, edges, j, x, t)
        slopes.append(a if a*t+b > 0 else Q(0))
    return sum((slopes[i+1]-slopes[i])*z**order for i,z in enumerate(cuts))


def functional(n, root, edges, order):
    partial = []
    for j in range(n):
        value = Q(0)
        others = [i for i in range(n) if i != j]
        for bits in product((0,1), repeat=n-1):
            x = [0]*n
            for i,v in zip(others,bits): x[i] = v
            value += (-1)**(n-1-sum(bits))*moment(n,root,edges,j,x,order)
        partial.append(str(value))
    return partial, str(sum(map(Q,partial)))


def main():
    n=5
    results=[]
    for root in range(1,n):
        for mask in range(1<<(n-2)):
            edges=[(v,1) if mask>>(v-2)&1 else (1,v) for v in range(2,n)]
            row={'root':root,'edges':edges,'orders':{}}
            for q in range(1,5):
                partial,total=functional(n,root,edges,q)
                row['orders'][str(q)]={'partial':partial,'total':total}
            results.append(row)
    out={'status':'EXACT_BOUNDED_MOMENT_PROBE_NO_QUOTIENT_BRIDGE','n':n,'target_total':-n,'results':results}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    for q in range(1,5):
        vals=sorted({Q(row['orders'][str(q)]['total']) for row in results})
        print('ORDER',q,'STAR_VALUES',list(map(str,vals)), 'TARGET',-n)


if __name__=='__main__': main()
