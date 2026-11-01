"""Construction search with one cross-pair first-layer function.

Seven translation-invariant functions plus two reference carriers give
first hidden layer width nine. Vanishing all interior kinks on every
braid cone and matching its generating rays would suffice globally.
The numerical dictionary solve is a candidate finder, never an exclusion.
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
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import lsqr


def positive_control():
    """Check the known fixed10 identity by these exact braid-cone equations."""
    net=json.loads(Path("netB_10_6.json").read_text())
    A=[[Q(c) for c in row] for row in net["first_layer"][:8]]
    W=[[Q(c) for c in row[:8]] for row in net["second_layer"][2:]]
    D=list(map(Q,net["output"][2:]));features={}
    for size in range(1,5):
        for S0 in itertools.combinations(range(5),size):
            S=frozenset(S0);f=[max(sum(row[i] for i in S),Q(0)) for row in A];features[S]=f
            value=f[0]+sum(d*max(sum(w*x for w,x in zip(row,f)),Q(0)) for d,row in zip(D,W))
            assert value==1-int(1 in S)
    for perm in itertools.permutations(range(5)):
        rays=[frozenset(perm[k:]) for k in range(1,5)];curvature={}
        for d,row in zip(D,W):
            v=tuple(sum(w*x for w,x in zip(row,features[S])) for S in rays)
            if min(v)>=0 or max(v)<=0:continue
            first=next(c for c in v if c);normal=tuple(c/first for c in v)
            curvature[normal]=curvature.get(normal,Q(0))+d*abs(first)
        assert all(c==0 for c in curvature.values())
    return {"status":"EXACT_KNOWN_FIXED10_BRAID_CONTROL_PASS","cones":120,"rays":30}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--box",type=int,default=1);ap.add_argument("--iterations",type=int,default=5000)
    ap.add_argument("--orientation",type=int,choices=range(4),default=0)
    args=ap.parse_args();start=time.monotonic();control=positive_control()
    # Row means sigma(x_i-x_j); final cross function is sigma(t-v).
    local=[((1,2),(3,4),(4,2)),((2,1),(3,4),(4,2)),
           ((2,1),(4,3),(4,2)),((2,1),(3,4),(2,4))][args.orientation]
    edges=[(1,0),(2,0),local[0],(3,0),(4,0),local[1],local[2]]
    rays=[frozenset(S) for k in range(1,5) for S in itertools.combinations(range(5),k)]
    features={S:tuple(int(i in S and j not in S) for i,j in edges) for S in rays}
    forms=[]
    for w in itertools.product(range(-args.box,args.box+1),repeat=7):
        first=next((c for c in w if c),None)
        if first is not None and first>0 and math.gcd(*w)==1:forms.append(w)
    W=np.asarray(forms,dtype=np.int64);ri=[];ci=[];vv=[];nr=0;cones=0
    for perm in itertools.permutations(range(5)):
        generator=[frozenset(perm[k:]) for k in range(1,5)]
        matrix=np.asarray([features[S] for S in generator],dtype=np.int64).T
        values=W@matrix;rowids={}
        for j,v0 in enumerate(values):
            if min(v0)>=0 or max(v0)<=0:continue
            v=tuple(map(int,v0));factor=math.gcd(*v);sgn=1 if next(c for c in v if c)>0 else -1
            normal=tuple(sgn*c//factor for c in v)
            if normal not in rowids:rowids[normal]=nr;nr+=1
            ri.append(rowids[normal]);ci.append(j+7);vv.append(factor)
        cones+=1
        if cones%30==0:print(json.dumps({"cones":cones,"kink_rows":nr,"nonzeros":len(vv),"seconds":time.monotonic()-start}),flush=True)
    for q,S in enumerate(rays):
        f=np.asarray(features[S],dtype=np.int64)
        for j,v in enumerate(f):
            if v:ri.append(nr+q);ci.append(j);vv.append(int(v))
        values=np.maximum(W@f,0)
        for j in np.flatnonzero(values):ri.append(nr+q);ci.append(int(j)+7);vv.append(int(values[j]))
    matrix=coo_matrix((vv,(ri,ci)),shape=(nr+30,len(forms)+7),dtype=float).tocsc();target=np.zeros(nr+30)
    for q,S in enumerate(rays):target[nr+q]=1-int(0 in S)
    result=lsqr(matrix,target,atol=1e-12,btol=1e-12,iter_lim=args.iterations);res=matrix@result[0]-target
    name="overnight_fixed_cross_dictionary_"+str(args.box)+(f"_orientation{args.orientation}" if args.orientation else "")
    record={"status":"NUMERICAL_CANDIDATE" if max(abs(res))<1e-8 else "NUMERICAL_RESIDUAL",
            "coefficient_box":args.box,"orientation":args.orientation,"first_layer_edges":edges,"forms":len(forms),"kink_rows":nr,"cones":cones,
            "shape":matrix.shape,"nonzeros":matrix.nnz,"solver_status":result[1],"iterations":result[2],
            "residual_max":float(max(abs(res))),"residual_l2":float(np.linalg.norm(res)),"seconds":time.monotonic()-start,
            "scope":"Finite integer dictionary; floating residuals do not prove existence or nonexistence",
            "positive_control":control,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if record["status"]=="NUMERICAL_CANDIDATE":np.savez_compressed(name+"_candidate.npz",forms=W,weights=result[0])
    Path(name+".json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n");print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
