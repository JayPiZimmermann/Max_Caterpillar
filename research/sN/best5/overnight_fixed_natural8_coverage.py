"""Independent exact flat/quadruple coverage for the natural8 layer.
Standard library only; no search or equation producer is imported.
"""
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path

A=[[-1,1,0,0,0],[-1,0,1,0,0],[0,1,-1,0,0],[-1,0,0,1,0],[-1,0,0,0,1],[0,0,0,1,-1]]


def rank(rows):
    a=[list(row) for row in rows];r=0
    if not a:return 0
    for j in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][j]),None)
        if p is None:continue
        a[r],a[p]=a[p],a[r];c=a[r][j];a[r]=[x/c for x in a[r]]
        for i in range(r+1,len(a)):
            c=a[i][j]
            if c:a[i]=[x-c*y for x,y in zip(a[i],a[r])]
        r+=1
    return r


def main():
    start=time.monotonic();raw=Path("overnight_fixed_natural8_inventory.json").read_bytes();inv=json.loads(raw)
    sets=[frozenset(c) for k in range(1,6) for c in itertools.combinations(range(5),k)]
    rel=[S for S in sets if len(S) in (3,4)]
    values={S:tuple(Q(max(sum(a[i] for i in S),0)) for a in A) for S in sets}
    assert rank(list(values.values()))==6
    def evaluate(B):return {S:tuple(sum(a*b for a,b in zip(values[S],v)) for v in B) for S in sets}
    def closure(v):return sum(1<<i for i,S in enumerate(rel) if not any(v[S]))
    B0=[[Q(int(i==j)) for i in range(6)] for j in range(6)];z0=closure(evaluate(B0));known={z0:B0};todo=[z0]
    while todo:
        z=todo.pop();B=known[z];vv=evaluate(B)
        for S in rel:
            form=vv[S]
            if not any(form):continue
            p=next(i for i,c in enumerate(form) if c)
            child=[[B[j][i]-form[j]/form[p]*B[p][i] for i in range(6)] for j in range(len(B)) if j!=p]
            zz=closure(evaluate(child))
            if zz not in known:known[zz]=child;todo.append(zz)
    assert len(known)==147 and known[(1<<15)-1]==[]
    saved={int(z):r for z,r in inv["flats"].items()};assert set(saved)=={z for z,B in known.items() if B}
    covers={}
    for z,row in saved.items():
        B=[[Q(c) for c in b] for b in row["basis"]]
        assert len(B)==len(known[z])==row["dimension"] and rank(B)==len(B)
        vv=evaluate(B);assert closure(vv)==z
        cubes={}
        for U in rel:
            if any(vv[U]):continue
            e={}
            for S in sets:
                if not S<U:continue
                v=vv[S];first=next((c for c in v if c),None)
                if first is None:continue
                f=tuple(c/first for c in v);e[f]=e.get(f,Q(0))+(-1)**(len(U)-len(S))*abs(first)
            cubes[U]=any(e.values())
        mask=0;q=0
        for U in (S for S in rel if len(S)==3):
            for o in range(5):
                if o in U:continue
                if not any(vv[U]) and not any(vv[U|{o}]) and cubes[U]:mask|=1<<q
                q+=1
        for j,U in enumerate(S for S in rel if len(S)==4):
            if not any(vv[U]) and cubes[U]:mask|=1<<(20+j)
        assert mask==row["cover"];covers[z]=mask
    zs=sorted(covers);full=(1<<25)-1;eligible={};quads=[];cover3=0
    for i,z1 in enumerate(zs):
        for j in range(i,len(zs)):
            z2=zs[j];pair=covers[z1]|covers[z2]
            for k in range(j,len(zs)):
                z3=zs[k];missing=full&~(pair|covers[z3])
                if not missing:cover3+=1
                if missing not in eligible:eligible[missing]=sum(1<<l for l,z in enumerate(zs) if covers[z]&missing==missing)
                bits=eligible[missing]&~((1<<k)-1)
                while bits:
                    bit=bits&-bits;l=bit.bit_length()-1;bits-=bit;quads.append((z1,z2,z3,zs[l]))
    assert cover3==0 and len(quads)==len(set(quads))==3418
    path=Path("overnight_fixed_natural8_coverage_quads.json");path.write_text(json.dumps(quads,separators=(",",":"))+"\n")
    result={"status":"INDEPENDENT_EXACT_NATURAL8_COVERAGE_PASS","flats_including_zero":147,"nonzero_flats":146,
        "covering_triples":cover3,"covering_quadruples":len(quads),"sign_cases":16*len(quads),
        "inventory_sha256":hashlib.sha256(raw).hexdigest(),"quads_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"seconds":time.monotonic()-start}
    Path("overnight_fixed_natural8_coverage.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
