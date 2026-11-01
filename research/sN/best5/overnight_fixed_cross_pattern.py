"""Continuous exact-pattern refinement of a sparse dictionary candidate.

Fix only its cone sign/cancellation pattern, and solve for all outer
coefficients anew. This searches real parameters, not the integer box.
An infeasible pattern is not an unrestricted lower bound.
"""
import argparse
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def refine(candidate,keep):
    edges=candidate["first_layer_edges"];nf=len(edges);A=[]
    for i,j in edges:
        a=[Q(0)]*5;a[i]=1;a[j]=-1;A.append(a)
    output=[Q(candidate["output"][k]) for k in keep];signs=[1 if d>0 else -1 for d in output]
    initial=[[abs(d)*Q(c) for c in candidate["outer_forms"][k]] for d,k in zip(output,keep)]
    K=len(keep);n=nf*(K+1);eq={};ineq={}
    def add(collection,row,rhs):
        v=tuple(row)+(-Q(rhs),);first=next((abs(c) for c in v if c),None)
        if first is not None:collection[tuple(c/first for c in v)]=None
    def expression(j,coefficient,active):
        row=[Q(0)]*n
        for f,a in enumerate(active):row[nf*(j+1)+f]=a[coefficient]
        return row
    for perm in itertools.permutations(range(5)):
        rank={label:i for i,label in enumerate(perm)};active=[a if rank[i]<rank[j] else [Q(0)]*5 for a,(i,j) in zip(A,edges)]
        forms=[tuple(sum(w*a[i] for w,a in zip(row,active)) for i in range(5)) for row in initial]
        linear=[[Q(0)]*n for _ in range(5)]
        for i in range(5):linear[i][:nf]=[a[i] for a in active]
        groups={}
        for j,g in enumerate(forms):
            if not any(g):
                for i in range(5):add(eq,expression(j,i,active),0)
                continue
            values=[sum(g[perm[p]] for p in range(k)) for k in range(1,5)]
            if min(values)>=0 or max(values)<=0:
                side=1 if min(values)>=0 else -1
                for k in range(1,5):
                    row=[Q(0)]*n
                    for f,a in enumerate(active):row[nf*(j+1)+f]=-side*sum(a[perm[p]] for p in range(k))
                    add(ineq,row,0)
                if side>0:
                    for i in range(5):linear[i]=[x+signs[j]*y for x,y in zip(linear[i],expression(j,i,active))]
            else:
                scale=next(c for c in g if c);normal=tuple(c/scale for c in g)
                groups.setdefault(normal,[]).append((j,scale))
        for group in groups.values():
            base,base_scale=group[0]
            assert sum(signs[j]*abs(scale/base_scale) for j,scale in group)==0
            for j,scale in group:
                ratio=scale/base_scale
                if j!=base:
                    for i in range(5):add(eq,[x-ratio*y for x,y in zip(expression(j,i,active),expression(base,i,active))],0)
                if ratio<0:
                    for i in range(5):linear[i]=[x+signs[j]*y for x,y in zip(linear[i],expression(j,i,active))]
        for i in range(5):add(eq,linear[i],int(i==perm[0])-int(i==0))
    E=np.asarray([[float(c) for c in row[:-1]] for row in eq]);b=-np.asarray([float(row[-1]) for row in eq])
    I=np.asarray([[float(c) for c in row[:-1]] for row in ineq]);ib=-np.asarray([float(row[-1]) for row in ineq])
    result=linprog(np.zeros(n),A_eq=E,b_eq=b,A_ub=I,b_ub=ib,bounds=[(None,None)]*n,method="highs")
    record={"solver_status":result.status,"message":result.message,"free_width":K,"equations":len(eq),"inequalities":len(ineq),"keep":keep}
    if result.x is not None:
        x=[Q(float(c)).limit_denominator(1000000) for c in result.x]
        assert all(sum(a*c for a,c in zip(row[:-1],x))+row[-1]==0 for row in eq)
        assert all(sum(a*c for a,c in zip(row[:-1],x))+row[-1]<=0 for row in ineq)
        record["candidate"]={"first_layer_edges":edges,"remainder":list(map(str,x[:nf])),
                             "outer_forms":[list(map(str,x[nf*(j+1):nf*(j+2)])) for j in range(K)],"output":list(map(str,signs))}
    return record


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--extra",type=int,default=0);args=ap.parse_args();start=time.monotonic()
    candidate=json.loads(Path("overnight_fixed_cross_sparsify_3_2000_candidate.json").read_text())
    essential=[4,10,13,14];other=[i for i in range(len(candidate["output"])) if i not in essential];records=[]
    for extra in itertools.combinations(other,args.extra):
        r=refine(candidate,essential+list(extra));records.append({k:v for k,v in r.items() if k!="candidate"})
        if "candidate" in r:
            Path(f"overnight_fixed_cross_pattern_{args.extra}_candidate.json").write_text(json.dumps(r["candidate"],indent=2)+"\n")
            print(json.dumps({k:v for k,v in r.items() if k!="candidate"}),flush=True);break
    result={"status":"EXACT_PATTERN_CANDIDATE" if records and "candidate" in r else "NO_FEASIBLE_PATTERN",
            "extra":args.extra,"records":records,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(f"overnight_fixed_cross_pattern_{args.extra}.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
