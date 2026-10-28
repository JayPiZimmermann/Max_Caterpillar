"""Minimize correction neurons beside a three-neuron cancellation core.

Each correction uses an arbitrary real coefficient vector in one of 206
non-kinking sign cones. Equal signs on a whole braid cone make its ReLU
linear there. Global equality is therefore imposed on all generating rays.
Finite parameter bounds and this core/pattern family are search restrictions.
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
from scipy.sparse import coo_matrix,load_npz
from overnight_fixed_cross_core_mip import build


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--core",type=int,default=0);ap.add_argument("--cap",type=int,default=10)
    ap.add_argument("--budget",type=int,default=300);ap.add_argument("--bound",type=int,default=8);args=ap.parse_args();start=time.monotonic()
    allW=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")["forms"]
    source=json.loads(Path("overnight_fixed_cross_core_search.json").read_text());cores=[r["key"]for r in source["records"]if len(r["key"])==3]
    edges=json.loads(Path("overnight_fixed_cross_dictionary_2_orientation3.json").read_text())["first_layer_edges"]
    n,signs,oldA,oldlo,oldhi=build(cores[args.core],edges,allW,1,args.bound);ncore=n-7;oldA=oldA.tocsr();prefix=oldA.shape[0]-120*24
    rays=[frozenset(S)for k in range(1,5)for S in itertools.combinations(range(5),k)]
    feature=np.asarray([[int(i in S and j not in S)for i,j in edges]for S in rays],dtype=np.int64)
    matrix=load_npz("overnight_fixed_cross_sparse_3_matrix.npz");ids=np.flatnonzero(matrix[:-30,7:].getnnz(axis=0)==0)
    patterns={}
    for j,p in zip(ids,np.sign(allW[ids]@feature.T).astype(np.int8)):patterns.setdefault(bytes(p),(int(j),p))
    groups=[(j,p,d)for j,p in patterns.values()for d in(1,-1)];ng=len(groups);nb=ncore+7*ng;nv=nb+ng
    ri=[];ci=[];vv=[];lo=[];hi=[]
    def add(e,l,h):
        row=len(lo)
        for j,c in e.items():
            if c:ri.append(row);ci.append(j);vv.append(float(c))
        lo.append(l);hi.append(h)
    for row in range(prefix):
        s,t=oldA.indptr[row:row+2];e={int(j):c for j,c in zip(oldA.indices[s:t],oldA.data[s:t])};assert all(j<ncore for j in e)
        add(e,oldlo[row],oldhi[row])
    permutation_index={p:i for i,p in enumerate(itertools.permutations(range(5)))}
    for r,S in enumerate(rays):
        perm=tuple(sorted(S))+tuple(sorted(set(range(5))-S));q=permutation_index[perm];e={}
        for coordinate in S:
            row=prefix+q*24+4+coordinate*4;s,t=oldA.indptr[row:row+2]
            for j,c in zip(oldA.indices[s:t],oldA.data[s:t]):
                if j<ncore:e[int(j)]=e.get(int(j),0)+c
        for k,(j,p,d)in enumerate(groups):
            if p[r]>0:
                for f,c in enumerate(feature[r]):
                    if c:e[ncore+7*k+f]=d*c
        target=1-int(0 in S);add(e,target,target)
    for k,(j,p,d)in enumerate(groups):
        offset=ncore+7*k;b=nb+k
        for r,row in enumerate(feature):
            e={offset+f:int(c)for f,c in enumerate(row)if c}
            add(e,0 if p[r]>=0 else -np.inf,0 if p[r]<=0 else np.inf)
        for f in range(7):
            add({offset+f:1,b:-args.bound},-np.inf,0)
            add({offset+f:1,b:args.bound},0,np.inf)
    add({nb+k:1 for k in range(ng)},-np.inf,args.cap)
    A=coo_matrix((vv,(ri,ci)),shape=(len(lo),nv)).tocsc()
    result=milp(c=np.r_[np.zeros(nb),np.ones(ng)],integrality=np.r_[np.zeros(nb,dtype=int),np.ones(ng,dtype=int)],
                bounds=Bounds(np.r_[np.full(nb,-args.bound),np.zeros(ng)],np.r_[np.full(nb,args.bound),np.ones(ng)]),
                constraints=LinearConstraint(A,np.asarray(lo),np.asarray(hi)),options={"time_limit":args.budget,"threads":1,"disp":True})
    record={"status":"BOUNDED_NO_CANDIDATE","solver_status":int(result.status),"message":result.message,"core":args.core,"cap":args.cap,
            "patterns":len(patterns),"variables":nv,"rows":len(lo),"bound":args.bound,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if result.x is not None:
        active=[k for k in range(ng)if result.x[nb+k]>.5];x=[Q(float(c)).limit_denominator(1000000)for c in result.x[:nb]]
        forms=[list(map(str,x[7*(j+1):7*(j+2)]))for j in range(3)]
        forms += [list(map(str,x[ncore+7*k:ncore+7*(k+1)]))for k in active]
        candidate={"first_layer_edges":edges,"remainder":list(map(str,x[:7])),"outer_forms":forms,
                   "output":list(map(str,signs+[groups[k][2]for k in active]))}
        name=f"overnight_fixed_cross_correction_mip_{args.core}";Path(name+"_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
        record.update(status="NUMERICAL_CORRECTION_CANDIDATE",correction_neurons=len(active),free_width=len(forms))
    Path(f"overnight_fixed_cross_correction_mip_{args.core}.json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
    print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
