#!/usr/bin/env python3
"""Independent controls for marked-path enumeration and batched arithmetic.
Budget30s, seed24102413. Rebuild cuts by graph traversal, not path position.
"""
import json,random,time,math
from pathlib import Path
import numpy as np
HERE=Path(__file__).parent;start=time.time();d=json.loads((HERE/'nc_marked_paths_8_family.json').read_text());uu=d['units'];oo=d['orbits'];P=1000003;n=8;rng=random.Random(24102413)
for u in rng.sample(uu,250):
    cuts=[]
    for x,y in u['edges']:
        side={x};todo=[x]
        while todo:
            v=todo.pop()
            for a,b in u['edges']:
                if (a,b)==(x,y):continue
                w=b if a==v else a if b==v else None
                if w is not None and w not in side:side.add(w);todo.append(w)
        sg=1
        if u['root'] in side:side=set(range(n))-{u['apex']}-side;sg=-1
        cuts.append([sorted(side),sg])
    assert cuts==u['cuts']
rng=random.Random(24102412);pp=[rng.randint(1,5)]
for _ in range(n-2):pp.append(sum(pp)+rng.randint(1,10))
pt=[-sum(pp)]+pp;rng.shuffle(pt);vals=[]
for u in uu:
    a=pt[u['apex']];den=1
    for side,s in u['cuts']:
        q=sum(pt[v] for v in side);den=den*q*(q+s*a)%P
    assert den;vals.append(pow(-a,n-4,P)*pow(den,P-2,P)%P)
row=[sum(vals[i] for i in orb)%P for orb in oo]+[(-1)**(n-1)*pow(math.prod(pt)%P,P-2,P)%P]
mat=np.load(HERE/'nc_marked_rows_8.npy',mmap_mode='r');assert row==mat[0].tolist()
assert time.time()-start<30
out=dict(status='CONTROLS_PASS',rebuilt_cut_units=250,independently_recomputed_full_rows=1,columns=len(row),seconds=time.time()-start)
(HERE/'nc_marked_batch_check.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
