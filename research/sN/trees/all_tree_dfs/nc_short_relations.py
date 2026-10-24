#!/usr/bin/env python3
"""Shorten modularly proposed kernel relations, without assuming identities.

The FLINT LLL proposal is checked by exact integer transformation and a
nonzero free-coordinate determinant. Each resulting rational-function identity
must still pass nc_obstruction.py independently.
"""
import sys,json,math,time
from pathlib import Path
from fractions import Fraction as Q
from flint import fmpz_mat

n=int(sys.argv[1]);here=Path(__file__).parent;start=time.time()
d=json.loads((here/f'nc_refined_{n}.json').read_text());m=d['orbits'];rows=[]
for r in d['kernel_proposals']:
    r=[(j,Q(c)) for j,c in r];scale=math.lcm(*(c.denominator for j,c in r));row=[0]*m
    for j,c in r:row[j]=int(c*scale)
    rows.append(row)
M=fmpz_mat(rows);L,T=M.lll(transform=True)
assert T*M==L and abs(T.det())==1
F=fmpz_mat([[L[i,j] for j in d['free_columns']] for i in range(len(rows))]);det=F.det();assert det
rels=[[(j,str(L[i,j])) for j in range(m) if L[i,j]] for i in range(len(rows))]
out={'n':n,'free_columns':d['free_columns'],'free_coordinate_determinant':str(det),'kernel_proposals':rels,
     'status':'INDEPENDENT_PROPOSALS_NOT_YET_IDENTITIES','elapsed_seconds':time.time()-start}
(here/f'nc_short_relations_{n}.json').write_text(json.dumps(out,indent=2)+'\n')
print('elapsed',out['elapsed_seconds'],'sizes',[len(r) for r in rels],flush=True)
