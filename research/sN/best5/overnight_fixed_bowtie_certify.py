"""Durable exact certificates for every fixed-bowtie K=3 case.

Cone witnesses refer directly to the 26 locality equations and (when
needed) 22 Boolean-ray equations. Every circuit carries its rational
linear relation. Hard cases carry closed-sign proof trees and the
compressed equation system, checked independently by row-space equality.
The old search verdicts only select the proof method; no verdict is proof.
"""
import argparse
import contextlib
import functools
import gzip
import hashlib
import itertools
import json
import signal
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import fastlp
from overnight_fixed_bowtie_k3 import FLATS,data
from overnight_fixed_bowtie import ALL,REL,VR
from overnight_fixed_bowtie_ray import ANN,TARGET,ray_problem
from overnight_fixed_circuits import block_circuits
from overnight_fixed_k2_certify import certified_feasible,COUNTS
from overnight_fixed_k2 import canonical


@functools.lru_cache(None)
def flat(z):
    B=[[Q(c) for c in b] for b in FLATS[z]["basis"]]
    ray={S:canonical(tuple(sum(a*b for a,b in zip(VR[S],v)) for v in B)) for S in ALL}
    forms=sorted({f for f,c in ray.values() if f is not None});ix={f:i for i,f in enumerate(forms)}
    cubes={U:{ix[f]:c for f,c in e.items()} for U,e in data(z)[1].items()}
    rays=[]
    for row in ANN:
        e={}
        for a,S in zip(row,[S for S in ALL if len(S)<5]):
            f,c=ray[S]
            if a and f is not None:e[ix[f]]=e.get(ix[f],Q(0))+a*c
        rays.append({i:c for i,c in e.items() if c})
    return forms,cubes,rays


def addexpr(out,e,c,shift=0):
    for i,a in e.items():
        j=i+shift;out[j]=out.get(j,Q(0))+c*a
        if not out[j]:del out[j]


def system(zs,ds,rays=False):
    blocks=[flat(z) for z in zs];offsets=[0]
    for f,_,_ in blocks:offsets.append(offsets[-1]+len(f))
    m=offsets[-1];rows=[];traces=[];orig=0
    # Eliminate only the two equations belonging to a triple. Retain the
    # exact row-operation trace back to the direct locality equations.
    for U in (S for S in REL if len(S)==3):
        outside=[o for o in range(5) if o not in U];a=[]
        for j,o in enumerate(outside):
            coefficients=[]
            for z,d in zip(zs,ds):
                zero=(z>>REL.index(U)&1) and (z>>REL.index(U|{o})&1)
                coefficients.append(Q(d if zero else 0))
            a.append(coefficients+[Q(2)]+[Q(int(i==j)) for i in range(2)])
        rr=0
        for c in range(3):
            p=next((i for i in range(rr,2) if a[i][c]),None)
            if p is None:continue
            a[rr],a[p]=a[p],a[rr];v=a[rr][c];a[rr]=[x/v for x in a[rr]]
            for i in range(2):
                if i!=rr and a[i][c]:
                    v=a[i][c];a[i]=[x-v*y for x,y in zip(a[i],a[rr])]
            rr+=1
        for row in a:
            if not any(row[:4]):continue
            e={}
            for k,c in enumerate(row[:3]):addexpr(e,blocks[k][1].get(U,{}),c,offsets[k])
            rows.append((e,row[3]));traces.append({orig+j:c for j,c in enumerate(row[4:]) if c})
        orig+=2
    for U in [S for S in REL if len(S)==4]+[frozenset(range(5))]:
        e={}
        for k,(z,d) in enumerate(zip(zs,ds)):
            if len(U)==5 or z>>REL.index(U)&1:addexpr(e,blocks[k][1].get(U,{}),Q(d),offsets[k])
        rows.append((e,Q(2*(-1)**(len(U)+1))));traces.append({orig:Q(1)});orig+=1
    if rays:
        for q,rhs in enumerate(TARGET):
            e={}
            for k,d in enumerate(ds):addexpr(e,blocks[k][2][q],Q(d),offsets[k])
            rows.append((e,rhs));traces.append({26+q:Q(1)})
    return m,offsets,rows,traces


def packed_farkas(cert,traces,cuts):
    ee={};yy={};cc=[]
    for (typ,i),raw in cert:
        c=Q(raw)
        if typ=="e":addexpr(ee,traces[i],c)
        elif typ=="y":yy[i]=yy.get(i,Q(0))+c
        else:
            assert typ=="c"
            relation,focus,_=cuts[i]
            cc.append([[[j,str(a)] for j,a in relation],focus,str(c)])
    return ["cone",[[i,str(c)] for i,c in sorted(ee.items()) if c],
            [[i,str(c)] for i,c in sorted(yy.items()) if c],cc]


def cone(zs,ds,rays=False,usecuts=False):
    m,offsets,rows,traces=system(zs,ds,rays)
    for i,(e,rhs) in enumerate(rows):
        if rhs and all(c*rhs<=0 for c in e.values()):
            s=Q(1) if rhs>0 else Q(-1)
            cert=[(["e",i],s)]+[(["y",j],-s*c) for j,c in e.items()]
            return packed_farkas(cert,traces,[])
    E=[(["e",i],[-rhs]+[e.get(j,Q(0)) for j in range(m)]) for i,(e,rhs) in enumerate(rows)]
    nonnegative=[(["y",i],[Q(0)]+[Q(int(i==j)) for j in range(m)]) for i in range(m)]
    cuts=[]
    if usecuts:
        # Relations on all ray forms, including forms eliminated from the
        # locality equations. They remain genuine nonnegative absolutes.
        for k,z in enumerate(zs):
            for relation in block_circuits(tuple(flat(z)[0]),4):
                rel=tuple((i+offsets[k],c) for i,c in relation)
                for focus,_ in rel:
                    row=[Q(0)]*(m+1)
                    for i,c in rel:row[i+1]=abs(c)*(-1 if i==focus else 1)
                    cuts.append((rel,focus,row))
    active=[];used=set()
    floatcuts=np.asarray([[float(x) for x in r[2][1:]] for r in cuts]) if cuts else None
    for _ in range(100):
        I=[(["c",i],cuts[i][2]) for i in active]
        allrows=[r for _,r in E+I]
        a=np.asarray([[float(c) for c in row[1:]] for row in allrows]);lo=-np.asarray([float(row[0]) for row in allrows])
        hi=np.full(len(allrows),np.inf);hi[:len(E)]=lo[:len(E)]
        name,y,_=fastlp.solve(np.zeros(m),a,lo,hi,np.zeros(m),np.full(m,np.inf))
        if name!="Optimal":
            feasible,cert=certified_feasible(E,nonnegative+I,m)
            if not feasible:return packed_farkas(cert,traces,cuts)
            return None
        if not cuts:return None
        violations=floatcuts@y
        new=[int(i) for i in np.argsort(violations) if violations[i]<-1e-8 and int(i) not in used][:40]
        if not new:return None
        active+=new;used.update(new)
    return None


def tree(zs,ds):
    p=ray_problem(zs,ds);assert p is not None
    n,offsets,rows=p;forms=sorted({f for e,r in rows for f in e});index={f:i for i,f in enumerate(forms)}
    exprs=[({index[f]:c for f,c in e.items()},r) for e,r in rows];signs={};I=[]
    for k in range(3):
        j=next((j for j,f in enumerate(forms) if any(f[offsets[k]:offsets[k+1]])),None)
        if j is not None:signs[j]=1;I.append((["f",j],[Q(0)]+list(forms[j])))
    def dfs(sg,pending,E,I):
        left=[];EE=list(E)
        for ei in pending:
            e,rhs=exprs[ei]
            if all(j in sg for j in e):
                row=[-rhs]+[sum(c*sg[j]*forms[j][p] for j,c in e.items()) for p in range(n)]
                if not any(row[1:]):
                    if row[0]:return ["constant",ei]
                    continue
                EE.append((["e",ei],row))
            else:left.append(ei)
        feasible,cert=certified_feasible(EE,I,n)
        if not feasible:return ["farkas",cert]
        if not left:raise RuntimeError("necessary-condition survivor")
        ei=min(left,key=lambda i:(sum(j not in sg for j in exprs[i][0]),len(exprs[i][0])))
        j=max((j for j in exprs[ei][0] if j not in sg),key=lambda j:sum(j in exprs[i][0] for i in left))
        children=[]
        for s in (1,-1):
            ss=dict(sg);ss[j]=s
            children.append(dfs(ss,left,EE,I+[(["f",j],[Q(0)]+[s*x for x in forms[j]])]))
        return ["split",j,*children]
    proof=dfs(signs,list(range(len(exprs))),[],I)
    return ["tree",{"n":n,"offsets":offsets,"forms":[list(map(str,f)) for f in forms],
                     "rows":[[[[i,str(c)] for i,c in sorted(e.items())],str(rhs)] for e,rhs in exprs]},proof]


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=1200);ap.add_argument("--limit",type=int,default=1000000)
    args=ap.parse_args();signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")))
    signal.alarm(args.budget);start=time.monotonic()
    path=Path("overnight_fixed_bowtie_proof.jsonl.gz");done=set()
    if path.exists():
        with gzip.open(path,"rt") as inp:
            for line in inp:
                r=json.loads(line);done.add((tuple(r["flats"]),tuple(r["signs"])))
    # Optional search hints only save unnecessary method attempts. A
    # fresh checkout needs no old search verdicts: without all three
    # hint logs, try the basic cone, strengthened cone, then sign tree.
    stage={};hint_count=0
    for level,name in enumerate(("relax","circuit","raycut")):
        hint=Path("overnight_fixed_bowtie_k3_"+name+".jsonl")
        if not hint.exists():continue
        hint_count+=1
        for line in hint.read_text().splitlines():
            r=json.loads(line);key=tuple(r["flats"]),tuple(r["signs"])
            if r["status"]=="EXCLUDED":stage[key]=level
    triples=json.loads(Path("overnight_fixed_bowtie_coverage_triples.json").read_text());counts=Counter();processed=0
    try:
        # Do not append an empty gzip member on a completed rerun.
        with (gzip.open(path,"at") if len(done)<8*len(triples) else contextlib.nullcontext(None)) as out:
            for zs in triples:
                for ds in itertools.product((1,-1),repeat=3):
                    key=tuple(zs),ds
                    if key in done:continue
                    if processed>=args.limit:raise StopIteration
                    level=stage.get(key,3 if hint_count==3 else 0)
                    proof=None
                    if level<3:proof=cone(zs,ds,rays=level>=2,usecuts=level>=1)
                    if proof is None:
                        if level<2:proof=cone(zs,ds,rays=True,usecuts=True)
                        if proof is None:proof=tree(zs,ds)
                    out.write(json.dumps({"flats":zs,"signs":ds,"proof":proof},separators=(",",":"))+"\n")
                    out.flush();processed+=1;counts[proof[0]]+=1
                    if processed%1000==0:print(json.dumps({"processed":processed,"counts":counts,"seconds":time.monotonic()-start}),flush=True)
    except (TimeoutError,StopIteration) as exc:
        print(json.dumps({"status":"BATCH_STOP","reason":str(exc),"processed":processed,"counts":counts,"seconds":time.monotonic()-start}),flush=True)
        return
    result={"status":"ALL_K3_PROOFS_PRODUCED","cases":len(done)+processed,"new_counts":counts,"seconds":time.monotonic()-start,
            "proof_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_bowtie_producer.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
