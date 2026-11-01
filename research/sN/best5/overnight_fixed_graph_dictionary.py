"""Construction search for alternative seven-comparison first hidden layers.
All failures concern the finite dictionary or bounded optimizer only.
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
from scipy.sparse import coo_matrix,hstack,save_npz
from scipy.sparse.linalg import lsqr
from overnight_fixed_cross_sparse import exact_check
from overnight_fixed_cross_dictionary import positive_control


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--graph",choices=["triangle_transitive","triangle_cycle","bowtie_reverse_head","bowtie_reverse_match"],required=True);args=ap.parse_args()
    start=time.monotonic();control=positive_control();edges=[(1,0),(2,0),(3,0),(4,0)]
    edges += {"triangle_transitive":[(2,1),(3,1),(3,2)],"triangle_cycle":[(2,1),(3,2),(1,3)],
              "bowtie_reverse_head":[(1,2),(3,4),(0,1)],"bowtie_reverse_match":[(1,2),(3,4),(2,1)]}[args.graph]
    forms=[]
    for w in itertools.product(range(-2,3),repeat=7):
        first=next((c for c in w if c),None)
        if first is not None and first>0 and math.gcd(*w)==1:forms.append(w)
    W=np.asarray(forms,dtype=np.int64);rays=[frozenset(S)for k in range(1,5)for S in itertools.combinations(range(5),k)]
    features={S:tuple(int(i in S and j not in S)for i,j in edges)for S in rays};ri=[];ci=[];vv=[];nr=0
    for perm in itertools.permutations(range(5)):
        V=np.asarray([features[frozenset(perm[:k])]for k in range(1,5)],dtype=np.int64).T;values=W@V;rowids={}
        for j,v0 in enumerate(values):
            if min(v0)>=0 or max(v0)<=0:continue
            v=tuple(map(int,v0));g=math.gcd(*v);sgn=1 if next(c for c in v if c)>0 else -1;normal=tuple(sgn*c//g for c in v)
            if normal not in rowids:rowids[normal]=nr;nr+=1
            ri.append(rowids[normal]);ci.append(j+7);vv.append(g)
    for q,S in enumerate(rays):
        f=np.asarray(features[S],dtype=np.int64)
        for j,v in enumerate(f):
            if v:ri.append(nr+q);ci.append(j);vv.append(int(v))
        values=np.maximum(W@f,0)
        for j in np.flatnonzero(values):ri.append(nr+q);ci.append(int(j)+7);vv.append(int(values[j]))
    A=coo_matrix((vv,(ri,ci)),shape=(nr+30,len(W)+7),dtype=float).tocsc();target=np.zeros(nr+30)
    for q,S in enumerate(rays):target[nr+q]=1-int(0 in S)
    prefix="overnight_fixed_graph_"+args.graph;save_npz(prefix+"_matrix.npz",A)
    fitted=lsqr(A,target,atol=1e-12,btol=1e-12,iter_lim=5000);res=A@fitted[0]-target
    record={"status":"NUMERICAL_CANDIDATE"if max(abs(res))<1e-8 else"NUMERICAL_RESIDUAL","edges":edges,
            "residual_max":float(max(abs(res))),"residual_l2":float(np.linalg.norm(res)),"iterations":fitted[2],
            "forms":len(W),"kink_rows":nr,"positive_control":control,"seconds":time.monotonic()-start}
    print(json.dumps(record,sort_keys=True),flush=True)
    np.savez_compressed(prefix+"_dictionary.npz",forms=W,weights=fitted[0])
    if record["status"]=="NUMERICAL_CANDIDATE":
        for size in(2000,5000):
            take=np.sort(np.argsort(abs(fitted[0][7:]))[::-1][:size]);C=hstack([A[:,:7],A[:,7+take]],format="csc");m=len(take)
            B=hstack([C[:,:7],C[:,7:],-C[:,7:]],format="csc")
            sparse=linprog(np.r_[np.zeros(7),np.ones(2*m)],A_eq=B,b_eq=target,
                           bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs",options={"time_limit":60})
            if sparse.x is None:continue
            vals=sparse.x[7:7+m]-sparse.x[7+m:];support=np.flatnonzero(abs(vals)>1e-7)
            R=[Q(float(c)).limit_denominator(1000000)for c in sparse.x[:7]];D=[Q(float(vals[j])).limit_denominator(1000000)for j in support]
            WW=[tuple(map(Q,map(int,W[take[j]])))for j in support]
            try:checked=exact_check(edges,WW,R,D)
            except AssertionError:continue
            candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row))for row in WW],"output":list(map(str,D))}
            Path(prefix+"_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
            record.update(status="EXACT_GLOBAL_BRAID_CANDIDATE_PASS",free_width=len(support),check=checked);break
    record.update(seconds=time.monotonic()-start,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(prefix+".json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n");print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
