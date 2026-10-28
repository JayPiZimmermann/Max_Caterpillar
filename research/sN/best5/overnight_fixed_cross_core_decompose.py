"""Decompose the lower-degree correction using all non-kinking dictionary forms.
The four-dimensional cone constraints have already been eliminated by the
exact core cancellation; only thirty global generating rays remain.
"""
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import load_npz
from overnight_fixed_cross_sparse import exact_check


def main():
    start=time.monotonic();source=json.loads(Path("overnight_fixed_cross_core_search.json").read_text());cores=[r["key"]for r in source["records"]if len(r["key"])==3]
    allW=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")["forms"]
    edges=json.loads(Path("overnight_fixed_cross_dictionary_2_orientation3.json").read_text())["first_layer_edges"]
    A=load_npz("overnight_fixed_cross_sparse_3_matrix.npz");ids=np.flatnonzero(A[:-30,7:].getnnz(axis=0)==0)
    W=allW[ids];ray=A[-30:,7+ids].toarray();feature=A[-30:,:7].toarray();m=len(ids)
    sets=[S for k in range(1,5)for S in itertools.combinations(range(5),k)];target=np.asarray([1-int(0 in S)for S in sets])
    patterns=np.sign(W@feature.T).astype(np.int8);best=10000;records=[];random=np.random.default_rng(502)
    for ci,core in enumerate(cores):
        corevalue=sum(float(Q(d))*np.maximum(feature@allW[j],0)for j,d in core)
        matrix=np.column_stack([feature,corevalue,ray,-ray])
        for iteration in range(20):
            prices=np.ones(m)if iteration==0 else np.exp(random.uniform(-1.5,1.5,m))
            result=linprog(np.r_[np.zeros(8),prices,prices],A_eq=matrix,b_eq=target,
                           bounds=[(None,None)]*7+[(0,None)]+[(0,None)]*(2*m),method="highs")
            if result.x is None:records.append({"core":ci,"iteration":iteration,"status":result.status});continue
            R=[Q(float(c)).limit_denominator(1000000)for c in result.x[:7]];scale=Q(float(result.x[7])).limit_denominator(1000000)
            vals=result.x[8:8+m]-result.x[8+m:];support=np.flatnonzero(abs(vals)>1e-7);groups={}
            for j in support:
                c=Q(float(vals[j])).limit_denominator(1000000);key=bytes(patterns[j]),1 if c>0 else -1
                if key not in groups:groups[key]=[Q(0)]*7
                groups[key]=[a+abs(c)*int(b)for a,b in zip(groups[key],W[j])]
            WW=[[scale*abs(Q(d))*int(c)for c in allW[j]]for j,d in core]
            D=[Q(1 if Q(d)>0 else -1)for j,d in core]
            WW.extend(groups.values());D.extend(Q(s)for p,s in groups)
            width=sum(any(c for c in row)for row in WW);r={"core":ci,"iteration":iteration,"width":width,"seconds":time.monotonic()-start};records.append(r)
            if width<best:
                try:control=exact_check(edges,WW,R,D)
                except AssertionError as exc:r.update(status="RATIONALIZATION_FAILED",failure=str(exc)[:100]);continue
                best=width;r.update(status="EXACT_GLOBAL_BRAID_PASS",check=control)
                candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row))for row in WW],"output":list(map(str,D))}
                Path("overnight_fixed_cross_core_decompose_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
                print(json.dumps(r,sort_keys=True),flush=True)
    result={"status":"EXACT_CORE_CORRECTION_SEARCH_COMPLETE","best_free_width":best,"records":records,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_core_decompose.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items()if k!="records"}),flush=True)


if __name__=="__main__":main()
