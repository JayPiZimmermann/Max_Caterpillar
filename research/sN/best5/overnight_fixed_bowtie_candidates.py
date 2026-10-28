"""Seek exact rational K=3 candidates with the actual bowtie remainder.

Adds all30 braid-ray equations and enforces exact vanishing-flat membership
through a positive LP margin. Only rational witnesses verified exactly are
reported; a failed/marginal floating solve is not an exclusion theorem.
Candidates are refuted on exact grid points before global cone verification.
"""
import argparse
import hashlib
import itertools
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import fastlp
import exact_lp
from overnight_fixed_bowtie import VR,ALL,REL
from overnight_fixed_bowtie_k3 import FLATS,problem
from overnight_fixed_k2 import canonical


def seek(zs,ds):
    p=problem(zs,ds)
    if p is None:return None,0
    gn,offsets,local=p;n=gn+8
    bases=[[[Q(c) for c in b] for b in FLATS[z]["basis"]] for z in zs]
    rows=[({tuple(f)+(Q(0),)*8:c for f,c in e.items()},[Q(0)]*n,r) for e,r in local]
    strict=set()
    for S in ALL:
        if len(S)==5:continue
        expr={}
        for k,basis in enumerate(bases):
            values=[sum(a*b for a,b in zip(VR[S],v)) for v in basis]
            lifted=[Q(0)]*offsets[k]+values+[Q(0)]*(n-offsets[k+1])
            f,scale=canonical(lifted)
            if f is not None:
                expr[f]=expr.get(f,Q(0))+ds[k]*scale
                if S in REL:strict.add(f)
        lin=[Q(0)]*gn+[2*x for x in VR[S]]
        rows.append((expr,lin,Q(2*(1-int(1 in S)))))
    forms=sorted({f for e,l,r in rows for f in e});signs={};I=[];nodes=[0]
    for k in range(3):
        f=next((f for f in forms if any(f[offsets[k]:offsets[k+1]])),None)
        if f is not None:signs[f]=1;I.append([Q(0)]+list(f))

    def witness(E,I,signs):
        # epsilon>0 is equivalent to strict membership. Its upper bound1
        # loses no positive feasible point and prevents an unbounded LP.
        allE=[row+[Q(0)] for row in E]
        allI=[row+[Q(0)] for row in I]
        allI += [[Q(0)]+[signs[f]*x for x in f]+[Q(-1)] for f in strict]
        allI += [[Q(1)]+[Q(0)]*n+[Q(-1)]]
        allrows=allE+allI;m=n+1
        a=np.asarray([[float(c) for c in row[1:]] for row in allrows]);rhs=-np.asarray([float(row[0]) for row in allrows])
        hi=np.full(len(allrows),np.inf);hi[:len(allE)]=rhs[:len(allE)]
        cost=np.zeros(m);cost[-1]=-1
        lb=np.full(m,-np.inf);lb[-1]=0
        name,xx,_=fastlp.solve(cost,a,rhs,hi,lb,np.full(m,np.inf))
        if name!="Optimal" or xx[-1]<=1e-9:return None
        def valid(x):
            return x[-1]>0 and all(row[0]+sum(a*b for a,b in zip(row[1:],x))==0 for row in allE) and all(row[0]+sum(a*b for a,b in zip(row[1:],x))>=0 for row in allI)
        rounded=[Q(float(x)).limit_denominator(10**6) for x in xx]
        if valid(rounded):return rounded[:-1]
        active=[row for row in allI if abs(float(row[0])+sum(float(a)*b for a,b in zip(row[1:],xx)))<1e-7]
        sol=exact_lp.solve_eq(allE+active,m)
        return sol[:-1] if sol is not None and valid(sol) else None

    def rec(signs,pending,E,I):
        nodes[0]+=1;EE=list(E);left=[]
        for expr,lin,rhs in pending:
            if all(f in signs for f in expr):
                row=[-rhs]+[lin[j]+sum(c*signs[f]*f[j] for f,c in expr.items()) for j in range(n)]
                if not any(row[1:]):
                    if row[0]:return None
                    continue
                EE.append(row)
            else:left.append((expr,lin,rhs))
        if not exact_lp.feasible(EE,I,n):return None
        if not left:return witness(EE,I,signs)
        expr,lin,rhs=min(left,key=lambda er:(sum(f not in signs for f in er[0]),len(er[0])))
        f=max((f for f in expr if f not in signs),key=lambda f:sum(f in e for e,l,r in left))
        for s in (1,-1):
            ss=dict(signs);ss[f]=s
            found=rec(ss,left,EE,I+[[Q(0)]+[s*x for x in f]])
            if found is not None:return found
        return None
    found=rec(signs,rows,[],I)
    if found is None:return None,nodes[0]
    coeffs=[]
    for k,basis in enumerate(bases):
        c=found[offsets[k]:offsets[k+1]]
        coeffs.append([sum(c[j]*basis[j][i] for j in range(len(basis))) for i in range(8)])
    for k,c in enumerate(coeffs):
        actual=sum(1<<i for i,S in enumerate(REL) if sum(a*b for a,b in zip(VR[S],c))==0)
        assert actual==zs[k]
    rp=found[gn:];r=[rp[i]-sum(Q(d)*c[i]/2 for d,c in zip(ds,coeffs)) for i in range(8)]
    net=json.loads(Path("netB_10_6.json").read_text())
    net["second_layer"]=[[str(x) for x in r]+["1","-1"],[str(-x) for x in r]+["-1","1"]]+[[str(x) for x in c]+["0","0"] for c in coeffs]
    net["output"]=["1","-1"]+[str(d) for d in ds]
    return net,nodes[0]


def evaluate(net,x):
    first=[max(sum(Q(a)*b for a,b in zip(row,x)),0) for row in net["first_layer"]]
    second=[max(sum(Q(a)*b for a,b in zip(row,first)),0) for row in net["second_layer"]]
    return sum(Q(a)*b for a,b in zip(net["output"],second))


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=1200)
    ap.add_argument("--case-budget",type=int,default=60);ap.add_argument("--limit",type=int,default=20)
    args=ap.parse_args()
    def timeout(*_):raise TimeoutError("case budget")
    signal.signal(signal.SIGALRM,timeout)
    inp=Path("overnight_fixed_bowtie_k3_dfs.jsonl").read_text();lines=inp.splitlines()
    if not inp.endswith("\n"):lines=lines[:-1]
    path=Path("overnight_fixed_bowtie_candidates.jsonl");done=set()
    if path.exists():
        for line in path.read_text().splitlines():
            r=json.loads(line)
            if r["status"]!="TIMEOUT":done.add((tuple(r["flats"]),tuple(r["signs"])))
    start=time.monotonic();processed=0
    with path.open("a") as out:
        for line in lines:
            r=json.loads(line)
            if r["status"]!="SURVIVOR":continue
            zs=tuple(r["flats"]);ds=tuple(r["signs"])
            if (zs,ds) in done:continue
            if processed>=args.limit or time.monotonic()-start>=args.budget:break
            signal.alarm(min(args.case_budget,max(1,int(args.budget-(time.monotonic()-start)))))
            t=time.monotonic();record={"flats":zs,"signs":ds}
            try:
                net,nodes=seek(zs,ds);record["nodes"]=nodes
                if net is None:record["status"]="NO_RATIONAL_WITNESS"
                else:
                    bad=None
                    for y in itertools.product((-2,-1,0,1,2),repeat=4):
                        x=(y[0],0,y[1],y[2],y[3]);v=evaluate(net,x)
                        if v!=max(x):bad={"x":x,"actual":str(v),"target":str(max(x))};break
                    record["network"]=net;record["counterexample"]=bad
                    record["status"]="EXACT_GRID_REFUTATION" if bad else "GRID_PASS_NEEDS_GLOBAL_CERTIFICATE"
            except TimeoutError:record["status"]="TIMEOUT"
            finally:signal.alarm(0)
            record["seconds"]=time.monotonic()-t
            out.write(json.dumps(record,separators=(",",":"))+"\n");out.flush()
            print(json.dumps({k:v for k,v in record.items() if k!="network"}),flush=True);processed+=1
    print(json.dumps({"status":"BATCH_COMPLETE","processed":processed,"seconds":time.monotonic()-start}),flush=True)


if __name__=="__main__":main()
