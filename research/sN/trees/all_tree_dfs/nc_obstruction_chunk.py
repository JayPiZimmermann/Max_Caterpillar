#!/usr/bin/env python3
"""Check selected NC8 kernel identities with bounded input memory.
Reads only units/orbits, excluding the large modular matrix. Each identity
gets an exact receipt with hashes of its input vectors and unit metadata.
"""
import sys,json,gzip,time,hashlib
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as Q
from rational_identity import add,Verifier

here=Path(__file__).parent;path=here/'nc_fast_8.json';lines=[]
with (path.open() if path.exists() else gzip.open(str(path)+'.gz','rt')) as f:
    for line in f:
        if line.startswith('  "points":'):break
        lines.append(line)
d=json.loads(''.join(lines)+'  "points": []\n}\n');units=d['units'];orbits=d['orbits'];del lines
w=json.loads((here/'nc_short_relations_8.json').read_text());n=8
fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
receipts=[]
indices=list(map(int,sys.argv[1:])) if len(sys.argv)>1 else range(json.loads((here/'nc_obstruction_8_short.json').read_text())['independent_exact_relations'],68)
for j in indices:
    v=Verifier(600)
    rel=w['kernel_proposals'][j];expr=defaultdict(Q);subset=[]
    for col,c in rel:
        for idx in orbits[col]:
            u=units[idx];subset.append(u);a=fs[u['apex']];den=[]
            for side,s in u['cuts']:
                q=tuple(sum(fs[t][k] for t in side) for k in range(n));den.extend([(q,1),(tuple(x+s*y for x,y in zip(q,a)),1)])
            add(expr,Q(c),tuple(-x for x in a),n-4,den)
    ok=v.check(expr);assert ok
    r={'index':j,'status':'EXACT_RATIONAL_IDENTITY','terms':len(expr),'elapsed_seconds':time.time()-v.start,
       'relation_sha256':hashlib.sha256(json.dumps(rel,sort_keys=True).encode()).hexdigest(),
       'units_sha256':hashlib.sha256(json.dumps(subset,sort_keys=True).encode()).hexdigest()}
    (here/f'nc_obstruction_8_identity_{j}.json').write_text(json.dumps(r,indent=2)+'\n');print(r,flush=True)
