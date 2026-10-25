#!/usr/bin/env python3
"""Exact locality-flat domain for the certified nine-row first hidden layer.

This only enumerates necessary domains. Nonempty covering triples are not
feasible networks and their existence or absence is recorded explicitly.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib,itertools,json,time

HERE=Path(__file__).resolve().parent
NETWORK=HERE/'overnight_fixed_cross_net9_17.json'


def rank(rows):
    work=[list(row) for row in rows];r=0
    if not work:return 0
    for j in range(len(work[0])):
        pivot=next((i for i in range(r,len(work)) if work[i][j]),None)
        if pivot is None:continue
        work[r],work[pivot]=work[pivot],work[r];p=work[r][j]
        work[r]=[v/p for v in work[r]]
        for i in range(r+1,len(work)):
            p=work[i][j]
            if p:work[i]=[x-p*y for x,y in zip(work[i],work[r])]
        r+=1
    return r


def main():
    started=time.monotonic();net=json.loads(NETWORK.read_text())
    A=[list(map(Q,row)) for row in net['first_layer'][:-2]]
    assert len(A)==7 and all(len(a)==5 and sum(a)==0 for a in A)
    sets=[frozenset(s) for k in range(1,6) for s in itertools.combinations(range(5),k)]
    relevant=[s for s in sets if len(s) in (3,4)]
    values={s:tuple(max(sum(a[i] for i in s),Q(0)) for a in A) for s in sets}
    assert rank(values.values())==7
    def evaluate(B):return {s:tuple(sum(a*b for a,b in zip(values[s],v)) for v in B) for s in sets}
    def closure(v):return sum(1<<i for i,s in enumerate(relevant) if not any(v[s]))
    initial=[[Q(i==j) for i in range(7)] for j in range(7)]
    z0=closure(evaluate(initial));known={z0:initial};todo=[z0]
    while todo:
        z=todo.pop();B=known[z];vv=evaluate(B)
        for s in relevant:
            form=vv[s]
            if not any(form):continue
            p=next(i for i,c in enumerate(form) if c)
            child=[[B[j][i]-form[j]/form[p]*B[p][i] for i in range(7)] for j in range(len(B)) if j!=p]
            zz=closure(evaluate(child))
            if zz not in known:known[zz]=child;todo.append(zz)
    flats={}
    for z,B in known.items():
        if not B:continue
        assert rank(B)==len(B)
        vv=evaluate(B);cubes={}
        for U in relevant:
            if any(vv[U]):continue
            terms={}
            for S in sets:
                if not S<U:continue
                form=vv[S];first=next((x for x in form if x),None)
                if first is None:continue
                normal=tuple(x/first for x in form)
                terms[normal]=terms.get(normal,Q(0))+(-1)**(len(U)-len(S))*abs(first)
            cubes[U]=any(terms.values())
        cover=0;index=0
        for U in (S for S in relevant if len(S)==3):
            for o in range(5):
                if o in U:continue
                if not any(vv[U]) and not any(vv[U|{o}]) and cubes[U]:cover|=1<<index
                index+=1
        for j,U in enumerate(S for S in relevant if len(S)==4):
            if not any(vv[U]) and cubes[U]:cover|=1<<(20+j)
        flats[z]=dict(basis=[list(map(str,b)) for b in B],dimension=len(B),cover=cover)
    zs=sorted(flats);full=(1<<25)-1;eligible={};triples=[];pairs=0
    for i,z1 in enumerate(zs):
        for j in range(i,len(zs)):
            z2=zs[j];missing=full&~(flats[z1]['cover']|flats[z2]['cover'])
            if not missing:pairs+=1
            if missing not in eligible:
                eligible[missing]=sum(1<<k for k,z in enumerate(zs) if flats[z]['cover']&missing==missing)
            bits=eligible[missing]&~((1<<j)-1)
            while bits:
                bit=bits&-bits;k=bit.bit_length()-1;bits-=bit;triples.append((z1,z2,zs[k]))
    assert len(triples)==len(set(triples))
    triple_path=HERE/'overnight_root9_triples.json'
    triple_path.write_text(json.dumps(triples,separators=(',',':'))+'\n')
    result=dict(status='EXACT_NECESSARY_NINE_ROW_LOCALITY_DOMAIN',features=A,
                flats_including_zero=len(known),nonzero_flats=len(flats),
                dimension_counts=dict(Counter(len(B) for B in known.values())),
                covering_pairs=pairs,covering_triples=len(triples),three_neuron_sign_cases=8*len(triples),
                flats=flats,seconds=time.monotonic()-started,
                network_sha256=hashlib.sha256(NETWORK.read_bytes()).hexdigest(),
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                triples_sha256=hashlib.sha256(triple_path.read_bytes()).hexdigest(),
                scope='Complete real flat coverage for necessary generic-tie equations; no feasibility or optimality claim.')
    result['features']=[list(map(str,a)) for a in A]
    (HERE/'overnight_root9_inventory.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='flats'}),flush=True)


if __name__=='__main__':main()
