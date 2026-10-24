#!/usr/bin/env python3
"""Assemble the exact NC8 obstruction from the completed budgeted checks.

The first run certified identities0..65; a second exact run certified66,67.
This checks their input hashes and the independence projection, and combines
the char0 rank upper bound with the exact modular augmented rank lower bound.
"""
import json,gzip,hashlib
from pathlib import Path
from fractions import Fraction as Q
H=Path(__file__).parent
partial=json.loads((H/'nc_obstruction_8_short.json').read_text());count=partial['independent_exact_relations'];assert 0<=count<=68
w=json.loads((H/'nc_short_relations_8.json').read_text());rs=w['kernel_proposals'];free=w['free_columns'];assert len(rs)==68
lines=[];p=H/'nc_fast_8.json'
with (p.open() if p.exists() else gzip.open(str(p)+'.gz','rt')) as f:
    for line in f:
        if line.startswith('  "points":'):break
        lines.append(line)
d=json.loads(''.join(lines)+'  "points": []\n}\n')
for j in range(count,68):
    r=json.loads((H/f'nc_obstruction_8_identity_{j}.json').read_text());assert r['status']=='EXACT_RATIONAL_IDENTITY'
    assert r['relation_sha256']==hashlib.sha256(json.dumps(rs[j],sort_keys=True).encode()).hexdigest()
    us=[d['units'][i] for col,c in rs[j] for i in d['orbits'][col]]
    assert r['units_sha256']==hashlib.sha256(json.dumps(us,sort_keys=True).encode()).hexdigest()
log=(H/'nc_obstruction_8_short.log').read_text()
assert all(f'IDENTITY {i} True ' in log for i in range(count))
P=1000003;basis={}
for rel in rs:
    a={j:Q(c) for j,c in rel};row=[a.get(f,Q(0)) for f in free]
    v=[c.numerator*pow(c.denominator,P-2,P)%P for c in row]
    for j,b in sorted(basis.items()):v=[(x-v[j]*y)%P for x,y in zip(v,b)]
    j=next(i for i,x in enumerate(v) if x);iv=pow(v[j],P-2,P);basis[j]=[x*iv%P for x in v]
assert len(basis)==68
mod=json.loads((H/'nc_refined_8.json').read_text());assert mod['modular_ranks']==[4097,4098]
star=json.loads((H/'star_obstruction_8.json').read_text());assert star['status']=='EXACT_ALL_STARS_RELATION'
assert star['modular_ranks']==[4100,4101]
out={'n':8,'status':'EXACT_RANK_OBSTRUCTION','labelled_full_units':len(d['units']),
     'dihedral_columns':len(d['orbits']),'independent_exact_relations':68,
     'rational_rank_upper':4097,'modular_augmented_rank':4098,
     'including_rooted_stars':{'columns':4169,'independent_exact_relations':69,'rational_rank_upper':4100,'modular_augmented_rank':4101},
     'scope':'All real coefficients and all face states of the fixed-circle original caterpillar dictionary; optionally all rooted-star face functions.'}
inputs=['nc_obstruction_8_short.json','nc_obstruction_8_short.log','nc_short_relations_8.json','nc_refined_8.json','star_obstruction_8.json']
inputs += [f'nc_obstruction_8_identity_{j}.json' for j in range(count,68)]
inputs += ['nc_fast_8.compression.json','rational_identity.py','nc_obstruction.py',
           'nc_obstruction_chunk.py','nc_refine.py','nc_short_relations.py','../dfs_review_nc8_coverage.json']
out['input_sha256']={name:hashlib.sha256((H/name).read_bytes()).hexdigest() for name in inputs}
out['producer_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(H/'nc_obstruction_8_certified.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
