"""Exact necessary locality inventory for natural8 construction search.

This is a search-space inventory, not a network-width exclusion. Every
nonzero real preactivation belongs to one of the listed exact flats.
"""
import hashlib
import itertools
import json
import time
from collections import Counter,defaultdict
from fractions import Fraction as Q
from pathlib import Path
from flats_loc import nullspace


def main():
    start=time.monotonic();sets=[frozenset(c) for k in range(1,6) for c in itertools.combinations(range(5),k)]
    rel=[S for S in sets if len(S) in (3,4)]
    def ray(S):
        x=[Q(int(i in S)) for i in range(5)];u,v,s,t=[x[i]-x[0] for i in range(1,5)]
        return tuple(max(a,0) for a in (u,v,u-v,s,t,s-t))
    values={S:ray(S) for S in sets};hyper=sorted({values[S] for S in rel if any(values[S])});flats={}
    for mask in range(1<<len(hyper)):
        B=nullspace([row for i,row in enumerate(hyper) if mask>>i&1],6)
        if not B:continue
        vv={S:tuple(sum(a*b for a,b in zip(values[S],v)) for v in B) for S in sets}
        z=sum(1<<i for i,S in enumerate(rel) if not any(vv[S]))
        if z in flats:continue
        cubes={}
        for U in rel:
            if any(vv[U]):continue
            e={}
            for S in sets:
                if not S<U:continue
                v=vv[S];c=next((c for c in v if c),None)
                if c is None:continue
                f=tuple(x/c for x in v);e[f]=e.get(f,Q(0))+(-1)**(len(U)-len(S))*abs(c)
            cubes[U]=any(e.values())
        cover=0;j=0
        for U in (S for S in rel if len(S)==3):
            for o in range(5):
                if o in U:continue
                if not any(vv[U]) and not any(vv[U|{o}]) and cubes[U]:cover|=1<<j
                j+=1
        for j,U in enumerate(S for S in rel if len(S)==4):
            if not any(vv[U]) and cubes[U]:cover|=1<<(20+j)
        flats[z]={"basis":[list(map(str,b)) for b in B],"dimension":len(B),"cover":cover}
    by=Counter(row["cover"] for row in flats.values());pairunions=Counter()
    for a,ca in by.items():
        for b,cb in by.items():pairunions[a|b]+=ca*cb
    full=(1<<25)-1
    ordered4=sum(ca*cb for a,ca in pairunions.items() for b,cb in pairunions.items() if a|b==full)
    ordered3=sum(ca*cb for a,ca in pairunions.items() for b,cb in by.items() if a|b==full)
    result={"status":"EXACT_NECESSARY_NATURAL8_INVENTORY","features":6,"unique_relevant_hyperplanes":len(hyper),
        "nonzero_flats":len(flats),"dimension_counts":dict(Counter(row["dimension"] for row in flats.values())),
        "coverage_masks":len(by),"covering_ordered_triples":ordered3,"covering_ordered_quadruples":ordered4,
        "pair_union_masks":len(pairunions),"flats":flats,"seconds":time.monotonic()-start,
        "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_natural8_inventory.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="flats"},sort_keys=True),flush=True)


if __name__=="__main__":main()
