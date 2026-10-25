#!/usr/bin/env python3
"""Exact symmetric graph-family gate; exponential number of labelled units.

Each graph has two interchangeable vertex classes, a distinguished head
root and apex. Uniform cross comparisons and within-class absolute
comparisons have coefficients in {-1,0,1}. For fixed parameters, all
label assignments number O(N^2 2^N), including graphs with cycles.
This is a gate for this specific uniform family, not all constructions.
"""
import argparse
from collections import defaultdict
from functools import reduce
from itertools import permutations, product, combinations
import hashlib, json, math, time
from pathlib import Path
from flint import fmpq_mat


def key_and_gradient(g):
    total = 0
    signs = []
    for v in g[:-1]:
        total += v
        signs.append(total)
    if min(signs) >= 0:
        return None, 0, g
    if max(signs) <= 0:
        return None, 0, (0,) * len(g)
    scale = reduce(math.gcd, g)
    first = next(v for v in g if v)
    orient = 1 if first > 0 else -1
    key = tuple(orient * v // scale for v in g)
    return key, scale, g if orient < 0 else (0,) * len(g)


def column(n, size, root, cross, left, right, perms, sides=None):
    a, b = sides if sides is not None else (
        tuple(range(1, size + 1)), tuple(range(size + 1, n)))
    cross_edges = tuple(product(a, b))
    left_edges = tuple(combinations(a, 2))
    right_edges = tuple(combinations(b, 2))
    walls = defaultdict(int)
    grad = [0] * n
    for p in perms:
        g = [0] * n
        g[p[root]] += 1
        g[p[0]] -= 1
        for u, v in cross_edges:
            i, j = p[u], p[v]
            if i < j:
                g[i] += cross
                g[j] -= cross
        for edges, coefficient in ((left_edges, left), (right_edges, right)):
            for u, v in edges:
                i, j = sorted((p[u], p[v]))
                g[i] += coefficient
                g[j] -= coefficient
        wall, scale, lin = key_and_gradient(tuple(g))
        if wall is not None:
            walls[wall] += scale
        for i, v in enumerate(lin):
            grad[i] += v
    return tuple(sorted(walls.items())), tuple(grad)


def star_column(n, root, inward, perms):
    walls = defaultdict(int)
    grad = [0] * n
    for p in perms:
        g = [0] * n
        g[p[root]] += 1
        g[p[0]] -= 1
        for leaf in range(2, n):
            u, v = (leaf, 1) if leaf in inward else (1, leaf)
            if p[u] < p[v]:
                g[p[u]] += 1
                g[p[v]] -= 1
        wall, scale, lin = key_and_gradient(tuple(g))
        if wall is not None:
            walls[wall] += scale
        for i, v in enumerate(lin):
            grad[i] += v
    return tuple(sorted(walls.items())), tuple(grad)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('n', type=int)
    parser.add_argument('--stars', action='store_true',
                        help='Adjoin every canonical star root/orientation orbit')
    parser.add_argument('--full', action='store_true',
                        help='Also allow comparisons incident to the distinguished apex')
    args = parser.parse_args()
    n = args.n
    assert 3 <= n <= 7
    started = time.monotonic()
    perms = tuple(permutations(range(n)))
    descriptors, cols, seen = [], [], set()
    # The linear remainder may contain the symmetric shallow comparison sum.
    shallow = ((), tuple(n - 1 - 2*i for i in range(n)))
    cols.append(shallow)
    descriptors.append({'shallow_absolute_sum': True})
    seen.add(shallow)
    for size in range(1, n - 1):
        for root in (1, size + 1):
            for cross, left, right in product((-1, 0, 1), repeat=3):
                col = column(n, size, root, cross, left, right, perms)
                if col in seen or not (col[0] or any(col[1])):
                    continue
                seen.add(col)
                cols.append(col)
                descriptors.append(dict(size=size, root=root, cross=cross,
                                        left=left, right=right))
        print('SIZE', size, 'COLUMNS', len(cols), 'SECONDS',
              round(time.monotonic()-started, 2), flush=True)
    if args.stars:
        for root in (1, 2):
            for bits in product((0, 1), repeat=n-2):
                inward = tuple(i+2 for i,b in enumerate(bits) if b)
                col = star_column(n, root, inward, perms)
                if col in seen or not (col[0] or any(col[1])):
                    continue
                seen.add(col)
                cols.append(col)
                descriptors.append(dict(star=True, root=root, inward=inward))
    if args.full:
        for size in range(1, n):
            for apex_in_left in (False, True):
                a = tuple(range(size)) if apex_in_left else tuple(range(1,size+1))
                b = tuple(i for i in range(n) if i not in a)
                roots = [next((i for i in side if i != 0), None) for side in (a,b)]
                for root in roots:
                    if root is None:
                        continue
                    for cross,left,right in product((-1,0,1),repeat=3):
                        col=column(n,size,root,cross,left,right,perms,(a,b))
                        if col in seen or not (col[0] or any(col[1])):
                            continue
                        seen.add(col);cols.append(col)
                        descriptors.append(dict(full=True,left_vertices=a,root=root,
                                                cross=cross,left=left,right=right))
            print('FULL SIZE',size,'COLUMNS',len(cols),'SECONDS',
                  round(time.monotonic()-started,2),flush=True)
    walls = sorted({k for c in cols for k, _ in c[0]})
    rows = [[0] * len(cols) for _ in range(len(walls) + n)]
    lookup = {w:i for i,w in enumerate(walls)}
    for j, (wc, grad) in enumerate(cols):
        for w, value in wc:
            rows[lookup[w]][j] = value
        for i, value in enumerate(grad):
            rows[len(walls)+i][j] = value
    # N max_N - sum_i x_i on the descending braid cone.
    target = [0] * len(walls) + [n-1] + [-1] * (n-1)
    matrix = fmpq_mat([row + [value] for row, value in zip(rows, target)])
    reduced, rank_aug = matrix.rref()
    rank_base = fmpq_mat(rows).rank()
    result = dict(n=n, status='EXACT_FAMILY_SPAN' if rank_base == rank_aug
                  else 'EXACT_FAMILY_OBSTRUCTION', ranks=[rank_base, rank_aug],
                  rows=len(rows), columns=len(cols),
                  distinct_interior_walls=len(walls), descriptors=descriptors,
                  seconds=time.monotonic()-started,
                  scope='Only the stated symmetric two-block graph family and symmetric shallow comparison remainder',
                  all_canonical_stars=args.stars,
                  full_comparison_graphs=args.full,
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if rank_base == rank_aug:
        sol = ['0'] * len(cols)
        for i in range(rank_aug):
            pivot = next(j for j in range(len(cols)) if reduced[i,j])
            sol[pivot] = str(reduced[i,len(cols)])
        result['solution'] = sol
    suffix = ('_stars' if args.stars else '') + ('_full' if args.full else '')
    path = Path(__file__).with_name(f'overnight_upper_bipartite_cycle_{n}{suffix}.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
                      ('descriptors','solution')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
