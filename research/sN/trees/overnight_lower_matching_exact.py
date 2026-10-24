#!/usr/bin/env python3
"""Exact finite-evaluation gate for seven-label trees of matching number <=2.

Phases `rows` and `solve`, each with a 1200-second budget. Row construction
uses common integer denominators, not rational reconstruction. Checkpoints
are saved after every exact row. Requires the existing research NumPy and
NetworkX environment; solve additionally uses the existing python-flint.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import sys
import time

import numpy as np

import networkx as nx
from dfs_review_fourier import family as raw_family

def family(m):
    units = []
    shapes = []
    for G0 in nx.nonisomorphic_trees(m-1):
        G = nx.convert_node_labels_to_integers(G0, first_label=1)
        shapes.append(dict(edges=sorted(G.edges()), matching=len(nx.max_weight_matching(G, maxcardinality=True))))
    for unit in raw_family(m, "all"):
        if len(nx.max_weight_matching(nx.Graph(unit["edges"]), maxcardinality=True)) <= 2:
            units.append(unit)
    return units, shapes
from dfs_review_fourier import orbit_exact

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
M = 7
P = 1000003
DEST = HERE/'overnight_lower_matching_rows_7.json'


def prepare():
    units,shapes = family(M)
    perms = np.array(list(itertools.permutations(range(M))),dtype=np.int64)
    cuts = [[(sum(1<<i for i in side),sgn) for side,sgn in u['cuts']] for u in units]
    needed = sorted({mask for es in cuts for mask,sgn in es})
    inv = np.zeros(P,dtype=np.int64); inv[1] = 1
    for j in range(2,P):
        inv[j] = P-(P//j)*inv[P%j]%P
    positive = list(itertools.combinations(range(10,20),6))
    random.Random(20261024).shuffle(positive)
    return units,shapes,perms,cuts,needed,inv,positive


def modular_row(pt,perms,cuts,needed,inv):
    om = np.array(pt,dtype=np.int64)[perms]
    apex = om[:,0]
    qs = {mask:om[:,[i for i in range(M) if mask>>i&1]].sum(axis=1)
          for mask in needed}
    num = (-apex)**(M-4)
    row = []
    for es in cuts:
        den = np.ones(len(perms),dtype=np.int64)
        for mask,sgn in es:
            q = qs[mask]%P
            den = den*q%P
            den = den*((qs[mask]+sgn*apex)%P)%P
        assert np.all(den != 0)
        row.append(int(((num%P)*inv[den]%P).sum()%P))
    row.append(int(((-1)**(M-1)*inv[math.prod(pt)%P])%P))
    return row


def exact_row(pt,perms,cuts,needed):
    om = np.array(pt,dtype=np.int64)[perms]
    apex = om[:,0]
    qs = {mask:om[:,[i for i in range(M) if mask>>i&1]].sum(axis=1)
          for mask in needed}
    numer = ((-apex)**(M-4)).tolist()
    bound = 2*abs(pt[0])
    common = math.lcm(*range(1,bound+1))**(2*(M-2))
    row = []
    for es in cuts:
        den = np.ones(len(perms),dtype=object)
        for mask,sgn in es:
            q = qs[mask]
            r = q+sgn*apex
            assert np.all(q != 0) and np.all(r != 0)
            assert np.max(np.abs(q)) <= bound and np.max(np.abs(r)) <= bound
            den *= q*r
        value = 0
        for num,d in zip(numer,den):
            q,rem = divmod(common,int(d))
            assert rem == 0
            value += num*q
        row.append(value)
    q,rem = divmod(common,math.prod(pt))
    assert rem == 0
    row.append((-1)**(M-1)*q)
    gcd = math.gcd(*row)
    assert gcd and common%gcd == 0
    return [v//gcd for v in row],common//gcd


def rows_phase():
    start = time.monotonic()
    units,shapes,perms,cuts,needed,inv,positive = prepare()
    bases = [{},{}]
    proposed = []

    def insert(row,basis):
        v = np.array(row,dtype=np.int64)%P
        for j,b in sorted(basis.items()):
            v = (v-v[j]*b)%P
        nz = np.flatnonzero(v)
        if len(nz):
            j = int(nz[0]); basis[j] = v*inv[v[j]]%P
            return True
        return False

    for pos in positive[:len(units)+30]:
        pt = (-sum(pos),)+pos
        row = modular_row(pt,perms,cuts,needed,inv)
        insert(row[:-1],bases[0])
        if insert(row,bases[1]):
            proposed.append((pt,row))
    print('PROPOSAL',len(units),'orbits','ranks',*map(len,bases),
          'selected rows',len(proposed),'seconds',round(time.monotonic()-start,3),flush=True)
    data = dict(arity=M,max_matching=2,representatives=units,shapes=shapes,
                prime=P,proposal_ranks=list(map(len,bases)),
                points=[],integer_rows=[],scales=[],modular_rows=[],
                expected_rows=len(proposed),budget_seconds=1200,
                status='EXACT_ROWS_IN_PROGRESS',fraction_controls=[],
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    perms_python = list(itertools.permutations(range(M)))
    for idx,(pt,modrow) in enumerate(proposed):
        if time.monotonic()-start >= 1200:
            data['status'] = 'EXACT_ROWS_BUDGET_EXHAUSTED'
            break
        vals,scale = exact_row(pt,perms,cuts,needed)
        assert [v%P for v in vals] == [v*(scale%P)%P for v in modrow]
        if idx in (0,len(proposed)-1):
            for j in (0,len(units)//2,len(units)-1):
                exact = orbit_exact(units[j],pt,M,perms_python)
                assert exact*scale == vals[j]
                data['fraction_controls'].append([idx,j])
        data['points'].append(pt)
        data['integer_rows'].append([str(v) for v in vals])
        data['scales'].append(str(scale))
        data['modular_rows'].append(modrow)
        data['elapsed_seconds'] = time.monotonic()-start
        DEST.write_text(json.dumps(data,indent=2)+'\n')
        print('EXACT ROW',idx+1,'of',len(proposed),'max digits',max(len(str(abs(v))) for v in vals),
              'seconds',round(time.monotonic()-start,3),flush=True)
    else:
        data['status'] = 'EXACT_ROWS_COMPLETE_NO_SEPARATOR_YET'
    data['elapsed_seconds'] = time.monotonic()-start
    DEST.write_text(json.dumps(data,indent=2)+'\n')
    print('DONE',data['status'],'rows',len(data['points']),'seconds',round(data['elapsed_seconds'],3),flush=True)


def solve_phase():
    start = time.monotonic()
    # Use the already installed research FLINT; do not install a dependency.
    sys.path.append(str(HERE.parent/'dfs/h5-growth/venv/lib/python3.12/site-packages'))
    from flint import fmpz_mat
    data = json.loads(DEST.read_text())
    assert data['status'] == 'EXACT_ROWS_COMPLETE_NO_SEPARATOR_YET'
    rows = [[int(v) for v in row] for row in data['integer_rows']]
    nrows = len(rows); ncols = len(rows[0])-1
    A = fmpz_mat([[rows[i][j] for i in range(nrows)] for j in range(ncols)])
    kernel,nullity = A.nullspace()
    print('EXACT NULLSPACE','shape',ncols,nrows,'nullity',nullity,
          'seconds',round(time.monotonic()-start,3),flush=True)
    certificate = None
    for c in range(nullity):
        weights = [int(kernel[i,c]) for i in range(nrows)]
        # Independent integer arithmetic verifies every claimed annihilation.
        assert all(sum(weights[i]*rows[i][j] for i in range(nrows)) == 0 for j in range(ncols))
        target = sum(weights[i]*rows[i][-1] for i in range(nrows))
        if not target:
            continue
        g = math.gcd(*weights)
        assert g
        weights = [v//g for v in weights]; target //= g
        certificate = dict(status='EXACT_FINITE_EVALUATION_SEPARATOR',arity=M,max_matching=2,
                           orbits=ncols,rows=nrows,ordinary_rank=nrows-nullity,
                           augmented_rank=nrows-nullity+1,
                           scaled_row_weights=[str(v) for v in weights],target_value=str(target),
                           rows_sha256=hashlib.sha256(DEST.read_bytes()).hexdigest(),
                           producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                           elapsed_seconds=time.monotonic()-start,budget_seconds=1200,
                           trust_boundary='Exact rational Fourier evaluations and full orbit coverage; not a Lean theorem')
        break
    if certificate is None:
        certificate = dict(status='NO_EXACT_SEPARATOR_IN_PROPOSED_ROWS',nullity=nullity,
                           elapsed_seconds=time.monotonic()-start)
    out = HERE/'overnight_lower_matching_separator_7.json'
    out.write_text(json.dumps(certificate,indent=2)+'\n')
    print('DONE',{k:v for k,v in certificate.items() if k not in {'scaled_row_weights','target_value'}},flush=True)
    if 'target_value' in certificate:
        print('TARGET NONZERO',int(certificate['target_value']) != 0,
              'target digits',len(certificate['target_value']),flush=True)


if __name__ == '__main__':
    if len(sys.argv)>1 and sys.argv[1] == 'solve':
        solve_phase()
    else:
        rows_phase()
