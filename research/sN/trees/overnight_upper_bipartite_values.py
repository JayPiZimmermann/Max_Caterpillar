#!/usr/bin/env python3
"""Independent value-certificate producer/checker for the two-class family.

Unlike the wall producer, this uses only integer evaluations of the actual
ReLU networks. `produce` uses FLINT to find a rational relation between
evaluation points. `check` uses the standard library and exhausts the raw
family, with no rank or cone routine and no import of the wall producer.
"""
import argparse, hashlib, itertools, json, math, random, time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).parent
N = 5
PERMS = tuple(itertools.permutations(range(N)))


def family():
    for size in range(1, N-1):
        for root in (1, size+1):
            for co in itertools.product((-1, 0, 1), repeat=3):
                yield ('block', size, root, *co)
    for root in (1, 2):
        for bits in itertools.product((0, 1), repeat=N-2):
            yield ('star', root, *bits)
    for size in range(1, N):
        for apex_in_left in (False,True):
            a=tuple(range(size)) if apex_in_left else tuple(range(1,size+1))
            b=tuple(i for i in range(N) if i not in a)
            for side in (a,b):
                root=next((i for i in side if i != 0),None)
                if root is not None:
                    for co in itertools.product((-1,0,1),repeat=3):
                        yield ('full',a,root,*co)


def evaluate(desc, point):
    value = 0
    if desc[0] in ('block','full'):
        _, split, root, cross, left, right = desc
        aa=tuple(range(1,split+1)) if desc[0]=='block' else split
        bb=tuple(range(split+1,N)) if desc[0]=='block' else tuple(i for i in range(N) if i not in aa)
        for perm in PERMS:
            x = tuple(point[i] for i in perm)
            a, b = tuple(x[i] for i in aa),tuple(x[i] for i in bb)
            inner = x[root]-x[0]
            inner += cross * sum(max(u-v, 0) for u in a for v in b)
            inner += left * sum(abs(u-v) for u,v in itertools.combinations(a,2))
            inner += right * sum(abs(u-v) for u,v in itertools.combinations(b,2))
            value += max(inner, 0)
    else:
        _, root, *bits = desc
        for perm in PERMS:
            x = tuple(point[i] for i in perm)
            inner = x[root]-x[0]
            for leaf, bit in enumerate(bits, 2):
                inner += max(x[leaf]-x[1] if bit else x[1]-x[leaf], 0)
            value += max(inner, 0)
    return value


def produce():
    from flint import fmpq_mat
    rng = random.Random(2592026)
    points = []
    while len(points) < 180:
        gaps = [rng.randrange(1,16) for _ in range(N-1)]
        point = tuple(sum(gaps[i:]) for i in range(N-1)) + (0,)
        if point not in points:
            points.append(point)
    descs = tuple(family())
    rows = []
    for i, point in enumerate(points):
        shallow = sum(abs(x-y) for x,y in itertools.combinations(point, 2))
        rows.append([shallow]+[evaluate(d,point) for d in descs])
        if i % 20 == 0:
            print('POINT', i, flush=True)
    target = [N*max(p)-sum(p) for p in points]
    eqs = [list(col)+[0] for col in zip(*rows)] + [target+[1]]
    reduced, rank = fmpq_mat(eqs).rref()
    weights = [Fraction(0)] * len(points)
    for i in range(rank):
        pivot = next(j for j in range(len(points)+1) if reduced[i,j])
        assert pivot < len(points), 'No value separator in selected points'
        weights[pivot] = Fraction(str(reduced[i,len(points)]))
    den = math.lcm(*(w.denominator for w in weights))
    terms = [(p,int(w*den)) for p,w in zip(points,weights) if w]
    payload = dict(n=N, target=N, raw_functions=len(descs),
                   points=[p for p,w in terms], weights=[w for p,w in terms],
                   target_value=den,
                   scope='Only the explicit finite two-class graph family (including full comparison graphs), all canonical stars, and symmetric pair-comparison remainder')
    (HERE/'overnight_upper_bipartite_values_certificate.json').write_text(
        json.dumps(payload,indent=2)+'\n')
    print('CERTIFICATE',len(terms),'points',flush=True)


def check():
    started = time.monotonic()
    path = HERE/'overnight_upper_bipartite_values_certificate.json'
    data = json.loads(path.read_text())
    points = [tuple(p) for p in data['points']]
    weights = data['weights']
    assert data['n'] == N and len(points) == len(weights)
    assert all(len(p)==N for p in points)
    assert sum(w*(N*max(p)-sum(p)) for p,w in zip(points,weights)) == data['target_value'] != 0
    assert sum(w*sum(abs(x-y) for x,y in itertools.combinations(p,2))
               for p,w in zip(points,weights)) == 0
    count = 0
    for desc in family():
        assert sum(w*evaluate(desc,p) for p,w in zip(points,weights)) == 0, desc
        count += 1
    assert count == data['raw_functions'] == 556
    print(json.dumps(dict(status='PASS_EXACT_INTEGER_VALUE_SEPARATOR',
                          raw_functions=count, points=len(points),
                          seconds=time.monotonic()-started,
                          certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                          source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          scope=data['scope']),indent=2),flush=True)


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['produce','check'])
    mode=parser.parse_args().mode
    produce() if mode=='produce' else check()
