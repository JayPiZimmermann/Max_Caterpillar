#!/usr/bin/env python3
"""Independent exhaustive rational checker for the nine-row P4 K3 exclusion.

Enumerates all subsets of the relevant hyperplanes, independently of the
producer's successive-intersection traversal. Verifies exact flat row spaces,
cover masks, complete triples/sign coverage, and every rational contradiction.
Only the standard library and the direct exact arithmetic checker are used.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib,itertools,json,time
import overnight_root9_equations as E

HERE=Path(__file__).resolve().parent


def main():
    started=time.monotonic();E.initialize();a=E.arithmetic
    inv=json.loads((HERE/'overnight_root9_inventory.json').read_text())
    hyperplanes=sorted({a.normalize(a.VALUE[S])[0] for S in a.REL if any(a.VALUE[S])})
    known={}
    for mask in range(1<<len(hyperplanes)):
        rr=a.rref([h for i,h in enumerate(hyperplanes) if mask>>i&1])
        pivots=[next(i for i,c in enumerate(row) if c) for row in rr];B=[]
        for free in range(7):
            if free in pivots:continue
            v=[Q(0)]*7;v[free]=1
            for p,row in zip(pivots,rr):v[p]=-row[free]
            B.append(v)
        zero=sum(1<<i for i,S in enumerate(a.REL)
                 if all(sum(x*y for x,y in zip(a.VALUE[S],v))==0 for v in B))
        known[zero]=B
    assert known[(1<<15)-1]==[] and len(known)==383
    assert set(a.BASES)=={z for z,B in known.items() if B}
    covers={}
    for z,B in a.BASES.items():
        assert a.rref(B)==a.rref(known[z]) and len(B)==inv['flats'][str(z)]['dimension']
        forms,cubes,rays=a.flat(z);cover=0
        for i,(U,o) in enumerate(a.LOCS[:-1]):
            active=z>>a.RIDX[U]&1
            if o is not None:active=active and z>>a.RIDX[U|{o}]&1
            if active and cubes[U]:cover|=1<<i
        assert cover==inv['flats'][str(z)]['cover'];covers[z]=cover
    bymask=Counter(covers.values());pairs=Counter()
    for u,cu in bymask.items():
        for v,cv in bymask.items():pairs[u|v]+=cu*cv
    full=(1<<25)-1
    assert pairs[full]==0
    ordered=sum(count*cv for union,count in pairs.items() for v,cv in bymask.items() if union|v==full)
    triples=json.loads((HERE/'overnight_root9_triples.json').read_text())
    assert len(triples)==len({tuple(t) for t in triples})==217 and ordered==6*len(triples)
    for t in triples:
        assert t==sorted(t) and len(set(t))==3 and all(z in covers for z in t)
        assert covers[t[0]]|covers[t[1]]|covers[t[2]]==full
    seen={tuple(t):0 for t in triples}
    for line in (HERE/'overnight_root9_cones.jsonl').read_text().splitlines():
        r=json.loads(line);zs=tuple(r['flats']);ds=tuple(r['signs'])
        assert r['status']=='EXACT_CONE_EXCLUSION' and zs in seen and len(ds)==3 and all(d in(-1,1) for d in ds)
        bit=1<<sum((d<0)<<i for i,d in enumerate(ds));assert not seen[zs]&bit;seen[zs]|=bit
        equation,forms,offsets=E.case_data(zs,ds);a.cone(r['proof'],equation,forms)
    assert all(mask==255 for mask in seen.values()) and a.COUNTS['cone']==1736
    names=['overnight_root9_inventory.json','overnight_root9_triples.json','overnight_root9_cones.jsonl',
           'overnight_root9_equations.py','overnight_fixed_bowtie_verify.py','overnight_fixed_cross_net9_17.json']
    result=dict(status='INDEPENDENT_EXACT_NINE_ROW_K3_EXCLUSION_PASS',
                relevant_hyperplanes=len(hyperplanes),flats_including_zero=len(known),
                covering_pairs=0,covering_triples=len(triples),sign_cases=1736,
                second_hidden_layer_lower_bound=6,seconds=time.monotonic()-started,
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                hashes={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in names},
                scope='All real preactivations and remainder in this fixed seven-feature span; translation-carrier bridge gives h2>=6. Matching construction remains open; not Lean.')
    (HERE/'overnight_root9_check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)


if __name__=='__main__':main()
