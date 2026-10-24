"""Independent proof-tree and equation checker. Standard library only.

This does not import the search, its equation reduction, or any LP solver.
It validates flat bases, regenerates unreduced signed cube equations,
checks rational row-space equivalence, and verifies every branch and
every Farkas contradiction by exact addition and multiplication.
"""
import gzip
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path

REL=[frozenset(c) for n in (3,4) for c in itertools.combinations(range(5),n)]
IDX={S:i for i,S in enumerate(REL)}
PAIR=list(itertools.combinations(range(5),2))
SETS=[frozenset(c) for n in range(1,6) for c in itertools.combinations(range(5),n)]
COUNTS={"cases":0,"basis":0,"split":0,"constant":0,"farkas":0,"formal_inconsistent":0,"equation_spaces":0}


def rref(matrix):
    if not matrix:return ()
    a=[list(row) for row in matrix]; rr=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(rr,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[rr],a[pivot]=a[pivot],a[rr]
        c=a[rr][j];a[rr]=[x/c for x in a[rr]]
        for i in range(len(a)):
            if i!=rr and a[i][j]:
                c=a[i][j];a[i]=[x-c*y for x,y in zip(a[i],a[rr])]
        rr+=1
    return tuple(tuple(row) for row in a[:rr])


def value(S,b):
    return sum(b[i] for i in S)+sum(b[5+j] for j,(u,v) in enumerate(PAIR) if u in S and v not in S)


def normalize(f):
    first=next((x for x in f if x),None)
    if first is None:return None,Q(0)
    # Choose the unique representative with first nonzero coefficient1.
    return tuple(x/first for x in f),abs(first)


def direct(zs,ds,bases):
    dims=[len(bases[z]) for z in zs];offsets=[0,dims[0],sum(dims)];n=sum(dims)
    formdata=[]
    for k,z in enumerate(zs):
        formdata.append({S:tuple([Q(0)]*offsets[k]+[value(S,b) for b in bases[z]]+[Q(0)]*(n-offsets[k+1])) for S in SETS})
    # Formal expressions for twice the mixed difference at a tied set.
    cubes={}
    for k in range(2):
        for U in SETS:
            if len(U)<3:continue
            expr={}
            for W in SETS:
                if W<U:
                    f,scale=normalize(formdata[k][W])
                    if f is not None:expr[f]=expr.get(f,Q(0))+(-1)**(len(U)-len(W))*scale
            cubes[k,U]={f:c for f,c in expr.items() if c}
    rows=[]
    for U in SETS:
        if len(U)<3:continue
        outs=[o for o in range(5) if o not in U] if len(U)==3 else [None]
        for outside in outs:
            expr={}
            for k,z in enumerate(zs):
                covered=(len(U)==5 or (z>>IDX[U]&1))
                if outside is not None:covered=covered and (z>>IDX[U|{outside}]&1)
                if not covered:continue
                assert not any(formdata[k][U])
                for f,c in cubes[k,U].items():expr[f]=expr.get(f,Q(0))+ds[k]*c
            rows.append(({f:c for f,c in expr.items() if c},Q(2*((-1)**(len(U)+1)))))
    return n,offsets,rows


def check_case(record,sysrecord,bases):
    assert all(record[k]==sysrecord[k] for k in ("case","flats","signs"))
    zs=record["flats"];ds=record["signs"]
    n,offsets,original=direct(zs,ds,bases)
    system=sysrecord["system"]
    original_forms={f for e,r in original for f in e}
    if system is None:
        assert record["proof"]==["formal_inconsistent"]
        forms=sorted(original_forms)
        matrix=[[e.get(f,Q(0)) for f in forms]+[-r] for e,r in original]
        reduced=rref(matrix)
        assert any(not any(row[:-1]) and row[-1] for row in reduced)
        COUNTS["formal_inconsistent"]+=1;return
    assert system["n"]==n and system["offsets"]==offsets
    forms=[tuple(Q(x) for x in f) for f in system["forms"]]
    assert forms==sorted(set(forms))
    exprs=[({int(i):Q(c) for i,c in terms},Q(r)) for terms,r in system["rows"]]
    combined=sorted(original_forms|set(forms))
    proposed=[({forms[i]:c for i,c in e.items()},r) for e,r in exprs]
    to_matrix=lambda rows:[[e.get(f,Q(0)) for f in combined]+[-r] for e,r in rows]
    assert rref(to_matrix(original))==rref(to_matrix(proposed))
    COUNTS["equation_spaces"]+=1
    signs={}
    # Every form is supported in exactly one neuron block. Therefore
    # independent global sign reversals preserve all absolute equations.
    for f in forms:
        assert len(f)==n and sum(any(f[offsets[k]:offsets[k+1]]) for k in range(2))==1
    for k in range(2):
        j=next((j for j,f in enumerate(forms) if any(f[offsets[k]:offsets[k+1]])),None)
        if j is not None:signs[j]=1

    def equality(ei,sg):
        expr,rhs=exprs[ei]
        assert all(j in sg for j in expr)
        return [-rhs]+[sum(c*sg[j]*forms[j][p] for j,c in expr.items()) for p in range(n)]

    def visit(node,sg):
        kind=node[0]
        if kind=="split":
            assert len(node)==4
            j=node[1];assert 0<=j<len(forms) and j not in sg
            for sign,child in zip((1,-1),node[2:]):
                ss=dict(sg);ss[j]=sign;visit(child,ss)
            COUNTS["split"]+=1
        elif kind=="constant":
            row=equality(node[1],sg)
            assert row[0] and not any(row[1:])
            COUNTS["constant"]+=1
        elif kind=="farkas":
            total=[Q(0)]*(n+1)
            for (typ,idx),coeff in node[1]:
                c=Q(coeff)
                if typ=="e":row=equality(idx,sg)
                else:
                    assert typ=="f" and idx in sg and c>=0
                    row=[Q(0)]+[sg[idx]*x for x in forms[idx]]
                total=[x+c*y for x,y in zip(total,row)]
            assert total[0]<0 and not any(total[1:])
            COUNTS["farkas"]+=1
        else:raise AssertionError(kind)
    visit(record["proof"],signs)


def main():
    started=time.monotonic()
    raw=json.loads(Path("overnight_fixed_k2_bases.json").read_text())
    bases={int(z):[[Q(x) for x in row] for row in rows] for z,rows in raw.items()}
    for z,basis in bases.items():
        assert z.bit_count()<=13 and len(basis)==14-z.bit_count()
        assert len(rref(basis))==len(basis)
        for b in basis:
            assert len(b)==15 and sum(b[:5])==0
            assert all(value(S,b)==0 for j,S in enumerate(REL) if z>>j&1)
        COUNTS["basis"]+=1
    expected={tuple(z) for z in json.loads(Path("overnight_fixed_coverage_pairs.json").read_text())}
    seen=set();indices={}
    with gzip.open("overnight_fixed_k2_proof.jsonl.gz","rt") as a,gzip.open("overnight_fixed_k2_systems.jsonl.gz","rt") as b:
        for line1,line2 in itertools.zip_longest(a,b):
            assert line1 and line2
            record=json.loads(line1);sysrecord=json.loads(line2)
            zs=tuple(record["flats"]);ds=tuple(record["signs"])
            assert zs in expected and ds in set(itertools.product((1,-1),repeat=2))
            assert (zs,ds) not in seen;seen.add((zs,ds))
            idx=record["case"]
            if idx in indices:assert indices[idx]==zs
            else:indices[idx]=zs
            check_case(record,sysrecord,bases);COUNTS["cases"]+=1
            if COUNTS["cases"]%400==0:print(json.dumps({"counts":COUNTS,"seconds":time.monotonic()-started}),flush=True)
    assert len(seen)==4*len(expected)==4772
    assert set(indices.values())==expected and set(indices)==set(range(1193))
    names=["overnight_fixed_k2_proof.jsonl.gz","overnight_fixed_k2_systems.jsonl.gz","overnight_fixed_k2_bases.json","overnight_fixed_coverage_pairs.json"]
    result={"status":"INDEPENDENT_EXACT_K2_EXCLUSION_PASS","counts":COUNTS,
            "seconds":time.monotonic()-started,"hashes":{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in names},
            "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope":"All real pair-feature preactivations, with free pair-feature remainder; mathematical locality bridge; not Lean"}
    Path("overnight_fixed_k2_check.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
