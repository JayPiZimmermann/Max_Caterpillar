"""Independent fixed-bowtie K=3 certificate checker: standard library only.

Rebuilds direct mixed differences from the actual first-layer rows; cone
proofs are checked against those equations, without equation reduction.
Short absolute-value circuits are accepted only after checking their
displayed linear dependence. Hard-case reduced systems are checked by
exact row-space equality, then every closed-sign tree is verified.
"""
import argparse
import functools
import gzip
import hashlib
import itertools
import json
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

SETS=[frozenset(c) for n in range(1,6) for c in itertools.combinations(range(5),n)]
REL=[S for S in SETS if len(S) in (3,4)];RIDX={S:i for i,S in enumerate(REL)}
LOCS=[(U,o) for U in SETS if len(U)==3 for o in range(5) if o not in U]
LOCS += [(U,None) for U in SETS if len(U) in (4,5)]
COUNTS=Counter()


def rref(matrix):
    if not matrix:return ()
    a=[list(row) for row in matrix];rr=0
    for j in range(len(a[0])):
        p=next((i for i in range(rr,len(a)) if a[i][j]),None)
        if p is None:continue
        a[rr],a[p]=a[p],a[rr];c=a[rr][j];a[rr]=[x/c for x in a[rr]]
        for i in range(len(a)):
            if i!=rr and a[i][j]:
                c=a[i][j];a[i]=[x-c*y for x,y in zip(a[i],a[rr])]
        rr+=1
    return tuple(tuple(row) for row in a[:rr])


def normalize(v):
    c=next((c for c in v if c),None)
    return (None,Q(0)) if c is None else (tuple(x/c for x in v),abs(c))


def add(out,e,c,shift=0):
    for j,a in e.items():
        i=j+shift;out[i]=out.get(i,Q(0))+c*a
        if not out[i]:del out[i]


def initialize():
    global BASES,VALUE,ANN,RHS
    receipt=json.loads(Path("overnight_fixed_bowtie_coverage.json").read_text())
    assert receipt["status"]=="INDEPENDENT_EXACT_BOWTIE_COVERAGE_PASS"
    for name,key in [("overnight_fixed_bowtie_inventory.json","inventory_sha256"),
                     ("netB_10_6.json","network_sha256"),
                     ("overnight_fixed_bowtie_coverage_triples.json","triples_sha256")]:
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==receipt[key]
    assert hashlib.sha256(Path("overnight_fixed_bowtie_coverage.py").read_bytes()).hexdigest()==receipt["checker_sha256"]
    inv=json.loads(Path("overnight_fixed_bowtie_inventory.json").read_text())
    BASES={int(z):[[Q(c) for c in b] for b in row["basis"]] for z,row in inv["flats"].items()}
    net=json.loads(Path("netB_10_6.json").read_text());A=[[Q(c) for c in a] for a in net["first_layer"][:8]]
    VALUE={S:[max(sum(a[i] for i in S),Q(0)) for a in A] for S in SETS}
    matrix=rref([[VALUE[S][j] for S in SETS[:-1]] for j in range(8)])
    piv=[next(i for i,c in enumerate(row) if c) for row in matrix]
    assert len(piv)==8
    ANN=[]
    for free in range(30):
        if free in piv:continue
        row=[Q(0)]*30;row[free]=Q(1)
        for p,r in zip(piv,matrix):row[p]=-r[free]
        assert all(sum(row[j]*VALUE[S][i] for j,S in enumerate(SETS[:-1]))==0 for i in range(8))
        ANN.append(row)
    assert len(ANN)==22
    RHS=[2*sum(a*(1-int(1 in S)) for a,S in zip(row,SETS[:-1])) for row in ANN]


@functools.lru_cache(None)
def flat(z):
    B=BASES[z]
    vv={S:tuple(sum(a*b for a,b in zip(VALUE[S],v)) for v in B) for S in SETS}
    assert sum(1<<i for i,S in enumerate(REL) if not any(vv[S]))==z
    rays={S:normalize(v) for S,v in vv.items()}
    forms=sorted({f for f,c in rays.values() if f is not None});ids={f:i for i,f in enumerate(forms)}
    cubes={}
    for U in SETS:
        if len(U)<3:continue
        e={}
        for S in SETS:
            if S<U:
                f,c=rays[S]
                if f is not None:add(e,{ids[f]:c},Q((-1)**(len(U)-len(S))))
        cubes[U]=e
    equations=[]
    for row in ANN:
        e={}
        for a,S in zip(row,SETS[:-1]):
            f,c=rays[S]
            if f is not None and a:add(e,{ids[f]:c},a)
        equations.append(e)
    return forms,cubes,equations


def case_data(zs,ds):
    blocks=[flat(z) for z in zs];off=[0]
    for f,_,_ in blocks:off.append(off[-1]+len(f))
    def equation(i):
        assert 0<=i<48
        e={}
        if i<26:
            U,o=LOCS[i]
            for k,(z,d) in enumerate(zip(zs,ds)):
                active=len(U)==5 or z>>RIDX[U]&1
                if o is not None:active=active and z>>RIDX[U|{o}]&1
                if active:add(e,blocks[k][1][U],Q(d),off[k])
            return e,Q(2*(-1)**(len(U)+1))
        for k,d in enumerate(ds):add(e,blocks[k][2][i-26],Q(d),off[k])
        return e,RHS[i-26]
    dims=[len(BASES[z]) for z in zs];coff=[0]
    for d in dims:coff.append(coff[-1]+d)
    forms=[]
    for k,(local,_,_) in enumerate(blocks):
        forms.extend(tuple([Q(0)]*coff[k]+list(f)+[Q(0)]*(coff[-1]-coff[k+1])) for f in local)
    return equation,forms,coff


def cone(proof,equation,forms):
    assert len(proof)==4
    total={};constant=Q(0)
    for i,c0 in proof[1]:
        c=Q(c0);e,rhs=equation(i);add(total,e,c);constant-=c*rhs
    for i,c0 in proof[2]:
        c=Q(c0);assert 0<=i<len(forms) and c>=0
        add(total,{i:Q(1)},c)
    for relation,focus,c0 in proof[3]:
        c=Q(c0);assert c>=0
        rel={int(i):Q(a) for i,a in relation}
        assert len(rel)==len(relation) and focus in rel and all(a for a in rel.values())
        assert all(0<=i<len(forms) for i in rel)
        assert all(sum(a*forms[i][j] for i,a in rel.items())==0 for j in range(len(forms[0])))
        add(total,{i:abs(a)*(-1 if i==focus else 1) for i,a in rel.items()},c)
        COUNTS["circuit_uses"]+=1
    assert constant<0 and not total,(constant,total)
    COUNTS["cone"]+=1


def tree(proof,equation,original_forms,coff):
    assert len(proof)==3;system=proof[1];n=coff[-1]
    assert system["n"]==n and system["offsets"]==coff
    forms=[tuple(Q(c) for c in f) for f in system["forms"]]
    assert forms==sorted(set(forms))
    exprs=[({int(i):Q(c) for i,c in e},Q(rhs)) for e,rhs in system["rows"]]
    allforms=sorted(set(original_forms)|set(forms));formids={f:i for i,f in enumerate(allforms)}
    direct=[]
    for i in range(48):
        e,rhs=equation(i);row=[Q(0)]*(len(allforms)+1);row[-1]=-rhs
        for j,c in e.items():row[formids[original_forms[j]]]+=c
        direct.append(row)
    proposed=[]
    for e,rhs in exprs:
        row=[Q(0)]*(len(allforms)+1);row[-1]=-rhs
        for j,c in e.items():row[formids[forms[j]]]+=c
        proposed.append(row)
    assert rref(direct)==rref(proposed)
    COUNTS["equation_spaces"]+=1
    sg={}
    for f in forms:assert len(f)==n and sum(any(f[coff[k]:coff[k+1]]) for k in range(3))==1
    for k in range(3):
        j=next((j for j,f in enumerate(forms) if any(f[coff[k]:coff[k+1]])),None)
        if j is not None:sg[j]=1
    def equality(i,s):
        e,rhs=exprs[i];assert all(j in s for j in e)
        return [-rhs]+[sum(c*s[j]*forms[j][p] for j,c in e.items()) for p in range(n)]
    def visit(node,s):
        kind=node[0]
        if kind=="split":
            assert len(node)==4;j=node[1];assert 0<=j<len(forms) and j not in s
            for sign,child in zip((1,-1),node[2:]):
                ss=dict(s);ss[j]=sign;visit(child,ss)
            COUNTS["split"]+=1
        elif kind=="constant":
            row=equality(node[1],s);assert row[0] and not any(row[1:]);COUNTS["constant"]+=1
        elif kind=="farkas":
            total=[Q(0)]*(n+1)
            for (typ,i),c0 in node[1]:
                c=Q(c0)
                if typ=="e":row=equality(i,s)
                else:
                    assert typ=="f" and i in s and c>=0
                    row=[Q(0)]+[s[i]*x for x in forms[i]]
                total=[x+c*y for x,y in zip(total,row)]
            assert total[0]<0 and not any(total[1:]);COUNTS["farkas"]+=1
        else:raise AssertionError(kind)
    visit(proof[2],sg);COUNTS["tree"]+=1


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--partial",action="store_true");args=ap.parse_args()
    start=time.monotonic();initialize()
    expected={tuple(z):0 for z in json.loads(Path("overnight_fixed_bowtie_coverage_triples.json").read_text())}
    with gzip.open("overnight_fixed_bowtie_proof.jsonl.gz","rt") as inp:
        for line in inp:
            record=json.loads(line);zs=tuple(record["flats"]);ds=tuple(record["signs"])
            assert zs in expected and len(ds)==3 and all(d in (-1,1) for d in ds)
            bit=1<<sum((d<0)<<i for i,d in enumerate(ds));assert not expected[zs]&bit;expected[zs]|=bit
            equation,forms,coff=case_data(zs,ds);proof=record["proof"]
            if proof[0]=="cone":cone(proof,equation,forms)
            else:assert proof[0]=="tree";tree(proof,equation,forms,coff)
            COUNTS["cases"]+=1
            if COUNTS["cases"]%5000==0:print(json.dumps({"counts":COUNTS,"seconds":time.monotonic()-start}),flush=True)
    complete=all(mask==255 for mask in expected.values())
    assert args.partial or complete
    names=["overnight_fixed_bowtie_proof.jsonl.gz","overnight_fixed_bowtie_inventory.json",
           "overnight_fixed_bowtie_coverage_triples.json","overnight_fixed_bowtie_coverage.json",
           "overnight_fixed_k2_check.json","netB_10_6.json"]
    result={"status":"INDEPENDENT_EXACT_BOWTIE_K3_EXCLUSION_PASS" if complete else "PARTIAL_PROOFS_VALID",
            "counts":COUNTS,"seconds":time.monotonic()-start,
            "hashes":{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in names},
            "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope":"All real preactivations and remainder in the eight zero-sum first-layer feature span; mathematical locality/translation bridge; not Lean"}
    Path("overnight_fixed_bowtie_check"+("_partial" if args.partial else "")+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
