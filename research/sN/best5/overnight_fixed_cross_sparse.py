"""Extract sparse rational candidates from the nine-row dictionary fits.

The LP is only a producer. Every rationalized candidate is separately
checked by exact whole-cone curvature cancellation and all generating rays.
"""
import argparse
import hashlib
import itertools
import json
import math
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,hstack,load_npz,save_npz


def matrices(orientation):
    prefix=f"overnight_fixed_cross_sparse_{orientation}"
    source=f"overnight_fixed_cross_dictionary_2_orientation{orientation}"
    record=json.loads(Path(source+".json").read_text());edges=record["first_layer_edges"]
    W=np.load(source+"_candidate.npz")["forms"]
    rays=[frozenset(S) for k in range(1,5) for S in itertools.combinations(range(5),k)]
    features={S:tuple(int(i in S and j not in S) for i,j in edges) for S in rays}
    if Path(prefix+"_matrix.npz").exists():
        A=load_npz(prefix+"_matrix.npz");nr=A.shape[0]-30
    else:
        ri=[];ci=[];vv=[];nr=0
        for perm in itertools.permutations(range(5)):
            generators=[frozenset(perm[k:]) for k in range(1,5)]
            matrix=np.asarray([features[S] for S in generators],dtype=np.int64).T
            values=W@matrix;rowids={}
            for j,v0 in enumerate(values):
                if min(v0)>=0 or max(v0)<=0:continue
                v=tuple(map(int,v0));factor=math.gcd(*v);sgn=1 if next(c for c in v if c)>0 else -1
                normal=tuple(sgn*c//factor for c in v)
                if normal not in rowids:rowids[normal]=nr;nr+=1
                ri.append(rowids[normal]);ci.append(j+7);vv.append(factor)
        for q,S in enumerate(rays):
            f=np.asarray(features[S],dtype=np.int64)
            for j,v in enumerate(f):
                if v:ri.append(nr+q);ci.append(j);vv.append(int(v))
            values=np.maximum(W@f,0)
            for j in np.flatnonzero(values):ri.append(nr+q);ci.append(int(j)+7);vv.append(int(values[j]))
        A=coo_matrix((vv,(ri,ci)),shape=(nr+30,len(W)+7),dtype=float).tocsc();save_npz(prefix+"_matrix.npz",A)
    target=np.zeros(nr+30)
    for q,S in enumerate(rays):target[nr+q]=1-int(0 in S)
    return edges,W,A,target


def exact_check(edges,W,R,D):
    """Global, not sampled: cancel every interior hyperplane on each braid cone."""
    features={};groups=0
    for size in range(1,5):
        for S0 in itertools.combinations(range(5),size):
            S=frozenset(S0);f=tuple(Q(int(i in S and j not in S)) for i,j in edges);features[S]=f
            value=sum(r*x for r,x in zip(R,f))+sum(d*max(sum(w*x for w,x in zip(row,f)),Q(0)) for d,row in zip(D,W))
            assert value==1-int(0 in S),(S,value)
    for perm in itertools.permutations(range(5)):
        rays=[frozenset(perm[k:]) for k in range(1,5)];curvature={}
        for d,row in zip(D,W):
            v=tuple(sum(w*x for w,x in zip(row,features[S])) for S in rays)
            if min(v)>=0 or max(v)<=0:continue
            first=next(c for c in v if c);normal=tuple(c/first for c in v)
            curvature[normal]=curvature.get(normal,Q(0))+d*abs(first)
        assert all(c==0 for c in curvature.values()),(perm,curvature)
        groups+=len(curvature)
    return {"cones":120,"rays":30,"curvature_groups":groups}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--orientation",type=int,choices=[2,3],default=2);ap.add_argument("--budget",type=int,default=300)
    args=ap.parse_args();start=time.monotonic();edges,W,A,target=matrices(args.orientation);m=len(W)
    print(json.dumps({"stage":"MATRIX_READY","shape":A.shape,"nonzeros":A.nnz,"seconds":time.monotonic()-start}),flush=True)
    B=hstack([A[:,:7],A[:,7:],-A[:,7:]],format="csc");objective=np.r_[np.zeros(7),np.ones(2*m)]
    result=linprog(objective,A_eq=B,b_eq=target,bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs",
                   options={"time_limit":args.budget,"presolve":True})
    record={"solver_status":result.status,"message":result.message,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    prefix=f"overnight_fixed_cross_sparse_{args.orientation}"
    if result.x is not None:
        values=result.x[7:7+m]-result.x[7+m:];support=np.flatnonzero(abs(values)>1e-7)
        record.update(support_size=len(support),objective=result.fun,residual_max=float(max(abs(A@np.r_[result.x[:7],values]-target))))
        R=[Q(float(c)).limit_denominator(1000000) for c in result.x[:7]]
        DD=[Q(float(values[j])).limit_denominator(1000000) for j in support];WW=[tuple(map(Q,map(int,W[j]))) for j in support]
        candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row)) for row in WW],"output":list(map(str,DD))}
        Path(prefix+"_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
        try:record.update(status="EXACT_GLOBAL_BRAID_CANDIDATE_PASS",check=exact_check(edges,WW,R,DD))
        except AssertionError as exc:record.update(status="RATIONALIZATION_FAILED",failure=str(exc)[:500])
    else:record["status"]="NO_SPARSE_CANDIDATE"
    Path(prefix+".json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n");print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
