"""Construction probe after retaining only one of the two reverse rows.

Seven zero-sum features plus the two coordinate carriers give first
width nine. Exact local-kink equations on the complete 3x4 product fan
are sufficient for a global identity. The numerical linear solver is
only a candidate finder; a nonzero residual is not an impossibility proof.
"""
import argparse
import hashlib
import itertools
import json
import math
import time
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import lsqr


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--box",type=int,default=2);args=ap.parse_args()
    start=time.monotonic();box=args.box
    # Group1=(sigma(u),sigma(v),sigma(u-v)); group2 has sigma(-t) too.
    C1=[((1,1,0),(1,0,1)),((1,1,0),(0,1,0)),((1,0,1),(0,0,1))]
    T1=[(1,1),(1,1),(1,0)]
    r=[(1,0,1,0),(1,1,0,0),(0,1,0,0),(0,0,0,1),(0,0,1,1)]
    C2=[(r[0],r[1]),(r[1],r[2]),(r[3],r[4]),(r[4],r[0])]
    T2=[(1,1),(1,1),(0,0),(0,1)]
    rowids={};rhs={};forms=[];columns=[]
    for i,j in itertools.product(range(3),range(4)):
        target=T1[i]+tuple(-c for c in T2[j])
        if min(target)<0 and max(target)>0:
            rowids[i,j,target]=len(rowids);rhs[rowids[i,j,target]]=1
    for w in itertools.product(range(-box,box+1),repeat=7):
        first=next((c for c in w if c),None)
        if first is None or first<0 or math.gcd(*w)!=1:continue
        left=[tuple(sum(a*b for a,b in zip(w[:3],r)) for r in c) for c in C1]
        right=[tuple(sum(a*b for a,b in zip(w[3:],r)) for r in c) for c in C2]
        col={}
        for i,j in itertools.product(range(3),range(4)):
            v=left[i]+right[j]
            if min(v)>=0 or max(v)<=0:continue
            factor=math.gcd(*v);sgn=1 if next(c for c in v if c)>0 else -1
            normal=tuple(sgn*c//factor for c in v);key=i,j,normal
            if key not in rowids:rowids[key]=len(rowids)
            col[rowids[key]]=factor
        forms.append(w);columns.append(col)
    rays=[S for k in range(1,5) for S in itertools.combinations(range(5),k)];features=[]
    for S in rays:
        x=[int(i in S) for i in range(5)];u,v,s,t=[x[i]-x[0] for i in range(1,5)]
        features.append([max(u,0),max(v,0),max(u-v,0),max(s,0),max(t,0),max(s-t,0),max(-t,0)])
    nlocal=len(rowids);ri=[];ci=[];vals=[]
    for c in range(7):
        for q,f in enumerate(features):
            if f[c]:ri.append(nlocal+q);ci.append(c);vals.append(f[c])
    for c,(w,col) in enumerate(zip(forms,columns),start=7):
        for r,v in col.items():ri.append(r);ci.append(c);vals.append(v)
        for q,f in enumerate(features):
            v=max(sum(a*b for a,b in zip(w,f)),0)
            if v:ri.append(nlocal+q);ci.append(c);vals.append(v)
    A=coo_matrix((vals,(ri,ci)),shape=(nlocal+30,len(forms)+7),dtype=float).tocsc();target=np.zeros(nlocal+30)
    for r,v in rhs.items():target[r]=v
    for q,S in enumerate(rays):target[nlocal+q]=1-int(0 in S)
    out=lsqr(A,target,atol=1e-12,btol=1e-12,iter_lim=10000);weights=out[0];res=A@weights-target
    result={"status":"NUMERICAL_DICTIONARY_CANDIDATE" if np.max(np.abs(res))<1e-8 else "NUMERICAL_DICTIONARY_RESIDUAL",
        "coefficient_box":box,"outer_forms":len(forms),"kink_rows":nlocal,"matrix_shape":A.shape,"nonzeros":A.nnz,
        "lsqr_status":out[1],"iterations":out[2],"residual_l2":float(np.linalg.norm(res)),"residual_max":float(np.max(np.abs(res))),
        "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Finite integer dictionary only; numerical solve is not an exclusion or a construction certificate"}
    name="overnight_fixed_nine_dictionary_"+str(box)
    if result["status"]=="NUMERICAL_DICTIONARY_CANDIDATE":np.savez_compressed(name+"_candidate.npz",forms=np.asarray(forms),weights=weights)
    Path(name+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
