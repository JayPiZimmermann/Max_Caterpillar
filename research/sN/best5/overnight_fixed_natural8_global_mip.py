"""Bounded constructive search with shared parameters on every flat.

At most five active flat/sign groups; at most one neuron per such group.
Absolute values are imposed with binary signs, not convexified. This is
a candidate finder only: finite bounds and one-copy restrictions prohibit
unrestricted negative conclusions. Any candidate needs rational/global
verification afterward.
"""
import argparse
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
from overnight_fixed_natural8_k4 import FLATS,SETS,REL,VR
from overnight_fixed_natural8_certify import flat,equations
from overnight_fixed_k2 import canonical


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--bound",type=float,default=10);ap.add_argument("--budget",type=int,default=600)
    ap.add_argument("--tag",default="10");args=ap.parse_args();start=time.monotonic();groups=[];pa=ya=0
    for z in sorted(FLATS):
        B=[[Q(c) for c in row] for row in FLATS[z]["basis"]];forms=flat(z)[0]
        strict={canonical(tuple(sum(a*b for a,b in zip(VR[S],v)) for v in B))[0] for S in REL};strict.discard(None)
        for sign in (1,-1):
            _,rows=equations([z],[sign]);groups.append({"z":z,"d":sign,"p":pa,"y":ya,"forms":forms,"strict":strict,"rows":rows,"dim":len(B)})
            pa+=len(B);ya+=len(forms)
    np_=pa;ny=ya;ng=len(groups);ns=np_+ny;nb=ns+ny;nv=nb+ng
    ri=[];ci=[];vv=[];lo=[];hi=[]
    def add(e,l,h):
        row=len(lo)
        for j,c in e.items():
            if c:ri.append(row);ci.append(j);vv.append(float(c))
        lo.append(l);hi.append(h)
    for row in range(50):
        e={}
        for group in groups:
            expr,rhs=group["rows"][row]
            for j,c in expr.items():e[np_+group["y"]+j]=c
        add(e,float(rhs),float(rhs))
    for k,group in enumerate(groups):
        for j,f in enumerate(group["forms"]):
            y=np_+group["y"]+j;s=ns+group["y"]+j;b=nb+k
            expr={group["p"]+i:c for i,c in enumerate(f) if c};neg={i:-c for i,c in expr.items()}
            add(expr|{y:-1},-np.inf,0);add(neg|{y:-1},-np.inf,0)
            add(neg|{y:1,s:2*args.bound},-np.inf,2*args.bound)
            add(expr|{y:1,s:-2*args.bound},-np.inf,0)
            add({y:1,b:-args.bound},-np.inf,0);add({s:1,b:-1},-np.inf,0)
            if f in group["strict"]:add({y:1,b:-.0001},0,np.inf)
        add({ns+group["y"]:1,nb+k:-1},0,0)
    add({nb+k:1 for k in range(ng)},-np.inf,5)
    for q in range(25):add({nb+k:1 for k,g in enumerate(groups) if FLATS[g["z"]]["cover"]>>q&1},1,np.inf)
    A=coo_matrix((vv,(ri,ci)),shape=(len(lo),nv)).tocsc()
    lower=np.r_[np.full(np_,-np.inf),np.zeros(ny),np.zeros(ny+ng)]
    upper=np.r_[np.full(np_,np.inf),np.full(ny,args.bound),np.ones(ny+ng)]
    res=milp(c=np.zeros(nv),integrality=np.r_[np.zeros(np_+ny,dtype=int),np.ones(ny+ng,dtype=int)],
        bounds=Bounds(lower,upper),constraints=LinearConstraint(A,np.asarray(lo),np.asarray(hi)),
        options={"time_limit":args.budget,"threads":1,"disp":True})
    result={"status":"BOUNDED_NO_CANDIDATE","solver_status":int(res.status),"message":res.message,
        "variables":nv,"parameters":np_,"absolute_forms":ny,"groups":ng,"constraints":len(lo),"nonzeros":A.nnz,
        "bound":args.bound,"strict_margin":"1/10000","one_neuron_per_flat_sign":True,"seconds":time.monotonic()-start,
        "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if res.x is not None:
        active=[k for k in range(ng) if res.x[nb+k]>.5]
        result["status"]="NUMERICAL_SHARED_PARAMETER_CANDIDATE";result["chosen"]=[[groups[k]["z"],groups[k]["d"]] for k in active]
        result["parameters_by_group"]=[list(map(float,res.x[groups[k]["p"]:groups[k]["p"]+groups[k]["dim"]])) for k in active]
    path=Path("overnight_fixed_natural8_global_"+args.tag+".json");path.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
