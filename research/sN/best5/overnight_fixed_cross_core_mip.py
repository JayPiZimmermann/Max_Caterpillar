"""Search a three-neuron cancellation core plus one unrestricted correction.

The core's cancellation pattern is fixed, but all coefficients are real
variables. The extra neuron must be linear on each braid cone; its signs
are chosen by the MILP. Coefficient bounds are constructive search limits,
so infeasibility or timeout does not establish a lower bound.
"""
import argparse
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix


def build(core,edges,allW,auxsign,bound):
    K=len(core);n=7*(K+2);A=[]
    for i,j in edges:
        a=[Q(0)]*5;a[i]=1;a[j]=-1;A.append(a)
    D=[Q(d)for j,d in core];signs=[1 if d>0 else -1 for d in D]
    initial=[[abs(d)*Q(int(c))for c in allW[j]]for(j,_),d in zip(core,D)]
    eq={};ineq={};cases=[]
    def save(collection,row):
        first=next((abs(c)for c in row if c),None)
        if first:collection[tuple(c/first for c in row)]=None
    def form(j,i,active):
        e=[Q(0)]*n
        for f,a in enumerate(active):e[7*(j+1)+f]=a[i]
        return e
    for perm in itertools.permutations(range(5)):
        rank={label:i for i,label in enumerate(perm)};active=[a if rank[i]<rank[j]else[Q(0)]*5 for a,(i,j)in zip(A,edges)]
        original=[tuple(sum(w*a[i]for w,a in zip(row,active))for i in range(5))for row in initial]
        linear=[[Q(0)]*n for _ in range(5)]
        for i in range(5):linear[i][:7]=[a[i]for a in active]
        groups={}
        for j,g in enumerate(original):
            if not any(g):
                for i in range(5):save(eq,form(j,i,active))
                continue
            values=[sum(g[perm[p]]for p in range(k))for k in range(1,5)]
            if min(values)>=0 or max(values)<=0:
                side=1 if min(values)>=0 else -1
                for k in range(1,5):
                    row=[Q(0)]*n
                    for f,a in enumerate(active):row[7*(j+1)+f]=side*sum(a[perm[p]]for p in range(k))
                    save(ineq,row)
                if side>0:
                    for i in range(5):linear[i]=[x+signs[j]*y for x,y in zip(linear[i],form(j,i,active))]
            else:
                scale=next(c for c in g if c);normal=tuple(c/scale for c in g);groups.setdefault(normal,[]).append((j,scale))
        for group in groups.values():
            base,base_scale=group[0];assert sum(signs[j]*abs(scale/base_scale)for j,scale in group)==0
            for j,scale in group:
                ratio=scale/base_scale
                if j!=base:
                    for i in range(5):save(eq,[x-ratio*y for x,y in zip(form(j,i,active),form(base,i,active))])
                if ratio<0:
                    for i in range(5):linear[i]=[x+signs[j]*y for x,y in zip(linear[i],form(j,i,active))]
        cases.append((perm,active,linear))
    ri=[];ci=[];vv=[];lo=[];hi=[]
    def add(e,l,h):
        q=len(lo)
        for j,c in enumerate(e):
            if c:ri.append(q);ci.append(j);vv.append(float(c))
        lo.append(l);hi.append(h)
    for row in eq:add(list(row)+[0]*120,0,0)
    for row in ineq:add(list(row)+[0]*120,0,np.inf)
    G=7*bound;M=(K+2)*G+1
    for q,(perm,active,linear)in enumerate(cases):
        for k in range(1,5):
            row=[Q(0)]*(n+120)
            for f,a in enumerate(active):row[7*(K+1)+f]=sum(a[perm[p]]for p in range(k))
            row[n+q]=-G;add(row,-G,0)
        for i in range(5):
            target=int(i==perm[0])-int(i==0);row=linear[i]+[0]*120
            row[n+q]=-M;add(row,-np.inf,target)
            row[n+q]=M;add(row,target,np.inf)
            row=[x+auxsign*y for x,y in zip(linear[i],form(K,i,active))]+[0]*120
            row[n+q]=M;add(row,-np.inf,target+M)
            row[n+q]=-M;add(row,target-M,np.inf)
    matrix=coo_matrix((vv,(ri,ci)),shape=(len(lo),n+120)).tocsc()
    return n,signs,matrix,np.asarray(lo),np.asarray(hi)


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=60);ap.add_argument("--bound",type=int,default=8);args=ap.parse_args()
    start=time.monotonic();source=json.loads(Path("overnight_fixed_cross_core_search.json").read_text());cores=[r["key"]for r in source["records"]if len(r["key"])==3]
    allW=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")["forms"]
    edges=json.loads(Path("overnight_fixed_cross_dictionary_2_orientation3.json").read_text())["first_layer_edges"]
    found=False;records=[]
    for index,core in enumerate(cores):
        for auxsign in(1,-1):
            n,signs,A,lo,hi=build(core,edges,allW,auxsign,args.bound)
            result=milp(c=np.zeros(n+120),integrality=np.r_[np.zeros(n,dtype=int),np.ones(120,dtype=int)],
                        bounds=Bounds(np.r_[np.full(n,-args.bound),np.zeros(120)],np.r_[np.full(n,args.bound),np.ones(120)]),
                        constraints=LinearConstraint(A,lo,hi),options={"time_limit":args.budget,"threads":1})
            r={"core_index":index,"auxsign":auxsign,"status":int(result.status),"message":result.message,"seconds":time.monotonic()-start}
            if result.x is not None:
                x=[Q(float(c)).limit_denominator(1000000)for c in result.x[:n]]
                candidate={"first_layer_edges":edges,"remainder":list(map(str,x[:7])),
                           "outer_forms":[list(map(str,x[7*(j+1):7*(j+2)]))for j in range(4)],"output":list(map(str,signs+[auxsign]))}
                Path("overnight_fixed_cross_core_mip_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
                r["candidate_found"]=True;found=True
            records.append(r);print(json.dumps(r,sort_keys=True),flush=True)
            if found:break
        if found:break
    record={"status":"NUMERICAL_PATTERN_CANDIDATE"if found else"BOUNDED_CORE_MIP_COMPLETE","bound":args.bound,"records":records,
            "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_core_mip.json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
    print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
