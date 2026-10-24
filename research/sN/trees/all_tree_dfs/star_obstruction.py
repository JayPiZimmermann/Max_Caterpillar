#!/usr/bin/env python3
"""Exact controls for adding the empty-cut rooted stars.
N6: certify every relation in the extended one-descent dictionary.
N8: certify the extra all-stars relation; combine with NC8's independent gate.
"""
import json,sys,time
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
from rational_identity import add,Verifier

n=int(sys.argv[1]);here=Path(__file__).parent;start=time.time();mode='desc1' if n==6 else 'nc'
d=json.loads((here/f'star_extension_{n}_{mode}.json').read_text())
if n==6:
    base=json.loads((here/'upper_fourier_6_desc1.json').read_text());units=base['units']+d['new_units'];orbits=[[i] for i in range(len(units))]
    rels=d['kernel_proposals'];free=d['free_columns']
    for j,r in enumerate(rels):
        rr={i:Q(c) for i,c in r};assert all(rr.get(f,0)==int(j==k) for k,f in enumerate(free))
else:
    units=d['new_units'];orbits=d['new_orbits'];rels=[[(j,'1') for j in range(len(orbits))]]
fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
v=Verifier(120);passed=0
for j,rel in enumerate(rels):
    e=defaultdict(Q)
    for col,c in rel:
        for i in orbits[col]:
            u=units[i];a=fs[u['apex']];den=[]
            for side,s in u['cuts']:
                q=tuple(sum(fs[t][k] for t in side) for k in range(n));den.extend([(q,1),(tuple(x+s*y for x,y in zip(q,a)),1)])
            add(e,Q(c),tuple(-x for x in a),n-4,den)
    assert v.check(e);passed+=1
status='EXACT_RANK_OBSTRUCTION' if n==6 else 'EXACT_ALL_STARS_RELATION'
if n==6:assert len(units)-passed<d['modular_ranks'][1]
out={'n':n,'status':status,'identities':passed,'elapsed_seconds':time.time()-start,'modular_ranks':d['modular_ranks']}
(here/f'star_obstruction_{n}.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
