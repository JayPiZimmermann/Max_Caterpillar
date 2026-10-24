"""Independent exact coverage of the fixed10-row K=3 search.

Uses recursive intersections of kernels, rather than subset enumeration,
to regenerate the complete vanishing-flat lattice. Recomputes every
potential mixed-difference contribution and every covering flat triple.
No producer module is imported; only Python's standard library is used.
"""
import hashlib
import itertools
import json
import time
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path


def rank(rows):
    a=[list(row) for row in rows]
    if not a:return 0
    rr=0
    for c in range(len(a[0])):
        p=next((i for i in range(rr,len(a)) if a[i][c]),None)
        if p is None:continue
        a[rr],a[p]=a[p],a[rr];v=a[rr][c];a[rr]=[x/v for x in a[rr]]
        for i in range(rr+1,len(a)):
            v=a[i][c]
            if v:a[i]=[x-v*y for x,y in zip(a[i],a[rr])]
        rr+=1
    return rr


def main():
    start=time.monotonic();raw=Path("overnight_fixed_bowtie_inventory.json").read_bytes();inv=json.loads(raw)
    netraw=Path("netB_10_6.json").read_bytes();net=json.loads(netraw)
    A=[[Q(c) for c in row] for row in net["first_layer"]]
    assert A[8:]==[[Q(0),Q(1),Q(0),Q(0),Q(0)],[Q(0),Q(-1),Q(0),Q(0),Q(0)]]
    assert all(sum(a)==0 for a in A[:8])
    sets=[frozenset(c) for k in range(1,6) for c in itertools.combinations(range(5),k)]
    rel=[S for S in sets if len(S) in (3,4)];idx={S:i for i,S in enumerate(rel)}
    val={S:tuple(max(sum(a[i] for i in S),0) for a in A[:8]) for S in sets}
    assert rank([val[S] for S in sets])==8
    evaluate=lambda B:{S:tuple(sum(a*b for a,b in zip(val[S],v)) for v in B) for S in sets}
    closure=lambda data:sum(1<<i for i,S in enumerate(rel) if not any(data[S]))
    initial=[[Q(int(i==j)) for i in range(8)] for j in range(8)]
    first=closure(evaluate(initial));known={first:initial};todo=[first]
    while todo:
        z=todo.pop();B=known[z];vv=evaluate(B)
        for S in rel:
            linear=vv[S]
            if not any(linear):continue
            p=next(i for i,c in enumerate(linear) if c)
            child=[[B[j][i]-linear[j]/linear[p]*B[p][i] for i in range(8)] for j in range(len(B)) if j!=p]
            zz=closure(evaluate(child))
            if zz not in known:known[zz]=child;todo.append(zz)
    assert len(known)==623 and known[(1<<15)-1]==[]
    nonzero={z:B for z,B in known.items() if B}
    saved={int(z):v for z,v in inv["flats"].items()}
    assert set(saved)==set(nonzero)
    covers={}
    for z,B in nonzero.items():
        old=[[Q(x) for x in b] for b in saved[z]["basis"]]
        assert len(old)==len(B)==saved[z]["dimension"] and rank(old)==len(old)
        oldval=evaluate(old);assert closure(oldval)==z
        # The independent lattice fixes the nullspace dimension. Thus the
        # producer basis spans the same real flat once independence and
        # all declared zero equations have been checked.
        for j,S in enumerate(rel):
            if z>>j&1:assert not any(oldval[S])
        vv=evaluate(B);nonlinear={}
        for U in sets:
            if len(U)<3 or any(vv[U]):continue
            expression={}
            for S in sets:
                if not S<U:continue
                f=vv[S];leading=next((c for c in f if c),None)
                if leading is None:continue
                key=tuple(c/leading for c in f)
                expression[key]=expression.get(key,Q(0))+(-1)**(len(U)-len(S))*abs(leading)
            nonlinear[U]=any(expression.values())
        mask=0;q=0
        for T in (S for S in rel if len(S)==3):
            for outside in range(5):
                if outside in T:continue
                if not any(vv[T]) and not any(vv[T|{outside}]) and nonlinear[T]:mask|=1<<q
                q+=1
        for q,U in enumerate(S for S in rel if len(S)==4):
            if not any(vv[U]) and nonlinear[U]:mask|=1<<(20+q)
        assert mask==saved[z]["cover"]
        covers[z]=mask
    zs=sorted(covers);allmask=(1<<25)-1;eligible={};triples=[]
    for i,z1 in enumerate(zs):
        for j in range(i,len(zs)):
            z2=zs[j];missing=allmask&~(covers[z1]|covers[z2])
            if missing not in eligible:
                eligible[missing]=sum(1<<k for k,z in enumerate(zs) if covers[z]&missing==missing)
            bits=eligible[missing]&~((1<<j)-1)
            while bits:
                bit=bits&-bits;k=bit.bit_length()-1;bits-=bit
                triples.append((z1,z2,zs[k]))
    by=defaultdict(list)
    for z,mask in covers.items():by[mask].append(z)
    proposed={tuple(sorted(zz)) for masks in inv["triple_masks"] for zz in itertools.product(*(by[m] for m in masks))}
    assert set(triples)==proposed and len(triples)==len(proposed)==30041
    out=Path("overnight_fixed_bowtie_coverage_triples.json")
    out.write_text(json.dumps(triples,separators=(",",":"))+"\n")
    result={"status":"INDEPENDENT_EXACT_BOWTIE_COVERAGE_PASS","features":8,"ray_rank":8,
            "flats_including_zero":len(known),"nonzero_flats":len(nonzero),"covering_triples":len(triples),
            "sign_cases":8*len(triples),"zero_coverage_flats":sum(mask==0 for mask in covers.values()),
            "inventory_sha256":hashlib.sha256(raw).hexdigest(),"network_sha256":hashlib.sha256(netraw).hexdigest(),
            "triples_sha256":hashlib.sha256(out.read_bytes()).hexdigest(),"checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "seconds":time.monotonic()-start,"scope":"Exact finite coverage; sign-case feasibility/exclusion checked separately."}
    Path("overnight_fixed_bowtie_coverage.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
