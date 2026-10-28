"""Bounded exact-sign candidate search for a selected natural8 pattern.

Binary variables impose actual absolute values of shared flat parameters,
not independent convexified values. Solver witnesses are rationally checked
before they are tested on an exact grid; global verification is still needed.
Negative outcomes concern only the declared bound/strictness and time limit.
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
import exact_lp
from overnight_fixed_natural8_k4 import FLATS,SETS,REL,VR,problem
from overnight_fixed_k2 import canonical
from overnight_fixed_natural8_candidates import evaluate


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--selection",default="overnight_fixed_natural8_select5_10_circuits_0.json")
    ap.add_argument("--bound",type=float,default=10);ap.add_argument("--budget",type=int,default=300);ap.add_argument("--tag",default="circuits_0")
    args=ap.parse_args();start=time.monotonic();chosen=json.loads(Path(args.selection).read_text())["chosen"]
    zs=[z for z,d in chosen];ds=[d for z,d in chosen];p=problem(zs,ds);assert p is not None
    n,off,rows=p;B=[[[Q(c) for c in b] for b in FLATS[z]["basis"]] for z in zs]
    fs={f for e,rhs in rows for f in e};strict=set()
    for k,basis in enumerate(B):
        for S in SETS[:-1]:
            v=[sum(a*b for a,b in zip(VR[S],v)) for v in basis]
            f,_=canonical(tuple([Q(0)]*off[k]+v+[Q(0)]*(n-off[k+1])))
            if f is not None:
                fs.add(f)
                if S in REL:strict.add(f)
    forms=sorted(fs);ix={f:i for i,f in enumerate(forms)};m=len(forms);nv=n+2*m;ri=[];ci=[];vv=[];lo=[];hi=[]
    def add(entries,lower,upper):
        row=len(lo)
        for j,c in entries.items():
            if c:ri.append(row);ci.append(j);vv.append(float(c))
        lo.append(lower);hi.append(upper)
    for e,rhs in rows:add({n+ix[f]:c for f,c in e.items()},float(rhs),float(rhs))
    for i,f in enumerate(forms):
        a={j:c for j,c in enumerate(f) if c};neg={j:-c for j,c in a.items()}
        add(dict(a,**{})|{n+i:-1},-np.inf,0)
        add(neg|{n+i:-1},-np.inf,0)
        add(neg|{n+i:1,n+m+i:2*args.bound},-np.inf,2*args.bound)
        add(a|{n+i:1,n+m+i:-2*args.bound},-np.inf,0)
    lb=np.r_[np.full(n,-np.inf),np.zeros(m),np.zeros(m)];ub=np.r_[np.full(n,np.inf),np.full(m,args.bound),np.ones(m)]
    for f in strict:lb[n+ix[f]]=1e-4
    for k in range(len(zs)):
        i=next(i for i,f in enumerate(forms) if any(f[off[k]:off[k+1]]));lb[n+m+i]=1
    A=coo_matrix((vv,(ri,ci)),shape=(len(lo),nv)).tocsc()
    res=milp(c=np.zeros(nv),integrality=np.r_[np.zeros(n+m,dtype=int),np.ones(m,dtype=int)],bounds=Bounds(lb,ub),
        constraints=LinearConstraint(A,np.asarray(lo),np.asarray(hi)),options={"time_limit":args.budget,"threads":1})
    record={"status":"BOUNDED_NO_CANDIDATE","solver_status":int(res.status),"message":res.message,"flats":zs,"signs":ds,
        "bound":args.bound,"strict_margin":"1/10000","parameter_dimension":n,"absolute_forms":m}
    if res.x is not None:
        signs=[1 if x>.5 else -1 for x in res.x[n+m:]]
        E=[[-rhs]+[sum(c*signs[ix[f]]*f[j] for f,c in e.items()) for j in range(n)] for e,rhs in rows]
        I=[[Q(-1,10000) if f in strict else Q(0)]+[s*c for c in f] for f,s in zip(forms,signs)]
        def valid(x):return all(r[0]+sum(a*b for a,b in zip(r[1:],x))==0 for r in E) and all(r[0]+sum(a*b for a,b in zip(r[1:],x))>=0 for r in I)
        x=[Q(float(c)).limit_denominator(10**6) for c in res.x[:n]]
        if not valid(x):
            active=[r for r in I if abs(float(r[0])+sum(float(a)*b for a,b in zip(r[1:],res.x[:n])))<1e-7]
            x=exact_lp.solve_eq(E+active,n)
        if x is None or not valid(x):record["status"]="UNRECONSTRUCTED_NUMERICAL_WITNESS"
        else:
            coefficients=[[sum(x[off[k]+j]*basis[j][i] for j in range(len(basis))) for i in range(6)] for k,basis in enumerate(B)]
            for k,c in enumerate(coefficients):assert sum(1<<i for i,S in enumerate(REL) if sum(a*b for a,b in zip(c,VR[S]))==0)==zs[k]
            remainder_eq=[]
            for S in SETS[:-1]:
                target=Q(1-int(0 in S))-sum(d*max(sum(a*b for a,b in zip(c,VR[S])),0) for d,c in zip(ds,coefficients))
                remainder_eq.append([-target]+list(VR[S]))
            r=exact_lp.solve_eq(remainder_eq,6);assert r is not None
            net={"N":5,"first_layer":[[-1,1,0,0,0],[-1,0,1,0,0],[0,1,-1,0,0],[-1,0,0,1,0],[-1,0,0,0,1],[0,0,0,1,-1],[1,0,0,0,0],[-1,0,0,0,0]],
                 "second_layer":[list(map(str,r))+["1","-1"],[str(-c) for c in r]+["-1","1"]]+[list(map(str,c))+["0","0"] for c in coefficients],
                 "output":["1","-1"]+list(map(str,ds))}
            bad=None
            for y in itertools.product((-2,-1,0,1,2),repeat=4):
                point=(0,)+y;actual=evaluate(net,point)
                if actual!=max(point):bad={"x":point,"actual":str(actual),"target":max(point)};break
            record["network"]=net;record["counterexample"]=bad
            record["status"]="EXACT_GRID_REFUTATION" if bad else "GRID_PASS_NEEDS_GLOBAL_CERTIFICATE"
            if bad is None:Path("overnight_fixed_natural8_absolute_"+args.tag+"_net.json").write_text(json.dumps(net,indent=2)+"\n")
    record["seconds"]=time.monotonic()-start;record["producer_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path("overnight_fixed_natural8_absolute_"+args.tag+".json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in record.items() if k!="network"},sort_keys=True),flush=True)


if __name__=="__main__":main()
