"""Exact global dictionary equations on the natural8 feature image.

Every product cone is parametrized by four nonnegative variables. Each
candidate outer neuron has either no interior kink or one hyperplane;
group proportional normals and equate their constant gradient jumps.
Together with Boolean rays, these linear equations are sufficient for a
global identity. Numerical solving is exploration only until rational
weights satisfy all integer equations and the resulting network passes
an independent global cone checker.
"""
import argparse
import hashlib
import itertools
import json
import math
import time
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix,hstack
from scipy.sparse.linalg import lsqr
from overnight_fixed_natural8_admissible import group


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--box",type=int,default=2);args=ap.parse_args()
    start=time.monotonic();box=args.box;forms=[];columns=[];rowids={};rhs={}
    rays=[S for k in range(1,5) for S in itertools.combinations(range(5),k)];features=[]
    for S in rays:
        x=[int(i in S) for i in range(5)];u,v,s,t=[x[i]-x[0] for i in range(1,5)]
        features.append([max(u,0),max(v,0),max(u-v,0),max(s,0),max(t,0),max(s-t,0)])
    for i,j in itertools.product(range(3),repeat=2):
        key=(i,j,(1,int(i!=2),-1,-int(j!=2)))
        rowids[key]=len(rowids);rhs[rowids[key]]=1
    for w in itertools.product(range(-box,box+1),repeat=6):
        first=next((c for c in w if c),None)
        if first is None or first<0 or math.gcd(*w)!=1:continue
        col={}
        for i,j in itertools.product(range(3),repeat=2):
            v=group(w[:3],i)+group(w[3:],j)
            if min(v)>=0 or max(v)<=0:continue
            factor=math.gcd(*v);sgn=1 if next(c for c in v if c)>0 else -1
            normal=tuple(sgn*c//factor for c in v);key=(i,j,normal)
            if key not in rowids:rowids[key]=len(rowids)
            col[rowids[key]]=factor
        forms.append(w);columns.append(col)
    nlocal=len(rowids);ri=[];ci=[];vals=[]
    for c in range(6):
        for q,f in enumerate(features):
            if f[c]:ri.append(nlocal+q);ci.append(c);vals.append(f[c])
    for c,(w,col) in enumerate(zip(forms,columns),start=6):
        for r,v in col.items():ri.append(r);ci.append(c);vals.append(v)
        for q,f in enumerate(features):
            v=max(sum(a*b for a,b in zip(w,f)),0)
            if v:ri.append(nlocal+q);ci.append(c);vals.append(v)
    A=coo_matrix((vals,(ri,ci)),shape=(nlocal+30,len(forms)+6),dtype=float).tocsc()
    target=np.zeros(nlocal+30)
    for r,v in rhs.items():target[r]=v
    for q,S in enumerate(rays):target[nlocal+q]=1-int(0 in S)
    out=lsqr(A,target,atol=1e-12,btol=1e-12,iter_lim=10000)
    x=out[0];res=A@x-target
    result={"status":"NUMERICAL_DICTIONARY_CANDIDATE" if np.max(np.abs(res))<1e-8 else "NUMERICAL_DICTIONARY_RESIDUAL",
        "coefficient_box":box,"outer_forms":len(forms),"kink_rows":nlocal,"matrix_shape":A.shape,"nonzeros":A.nnz,
        "lsqr_status":out[1],"iterations":out[2],"residual_l2":float(np.linalg.norm(res)),"residual_max":float(np.max(np.abs(res))),
        "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Finite integer dictionary only; numerical solve is not an exclusion or a construction certificate"}
    name="overnight_fixed_natural8_dictionary_"+str(box)
    if result["status"]=="NUMERICAL_DICTIONARY_CANDIDATE":
        np.savez_compressed(name+"_candidate.npz",forms=np.asarray(forms),weights=x)
    Path(name+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
