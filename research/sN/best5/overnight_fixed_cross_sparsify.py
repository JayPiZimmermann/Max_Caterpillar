"""Bounded positive search for fewer outer terms in the nine-row model."""
import argparse
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import hstack
from overnight_fixed_cross_sparse import matrices,exact_check


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--orientation",type=int,choices=[2,3],default=2)
    ap.add_argument("--columns",type=int,default=2000);ap.add_argument("--rounds",type=int,default=40)
    args=ap.parse_args();start=time.monotonic();edges,allW,allA,target=matrices(args.orientation)
    z=np.load(f"overnight_fixed_cross_dictionary_2_orientation{args.orientation}_candidate.npz")
    take=np.sort(np.argsort(abs(z["weights"][7:]))[::-1][:args.columns]);W=allW[take]
    A=hstack([allA[:,:7],allA[:,7+take]],format="csc");m=len(W);B=hstack([A[:,:7],A[:,7:],-A[:,7:]],format="csc")
    random=np.random.default_rng(619);best=100000;union=set();records=[]
    prefix=f"overnight_fixed_cross_sparsify_{args.orientation}_{args.columns}"
    for iteration in range(args.rounds):
        prices=np.ones(m) if iteration==0 else np.exp(random.uniform(-2,2,m))
        result=linprog(np.r_[np.zeros(7),prices,prices],A_eq=B,b_eq=target,
                       bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs",options={"time_limit":15})
        if result.x is None:
            records.append({"iteration":iteration,"status":result.status});continue
        values=result.x[7:7+m]-result.x[7+m:];support=np.flatnonzero(abs(values)>1e-7);union.update(int(take[j]) for j in support)
        record={"iteration":iteration,"support":len(support),"seconds":time.monotonic()-start};records.append(record)
        if len(support)<best:
            R=[Q(float(c)).limit_denominator(1000000) for c in result.x[:7]]
            D=[Q(float(values[j])).limit_denominator(1000000) for j in support];WW=[tuple(map(Q,map(int,W[j]))) for j in support]
            try:
                control=exact_check(edges,WW,R,D);best=len(support)
                candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row)) for row in WW],"output":list(map(str,D))}
                Path(prefix+"_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
                record.update(status="EXACT_GLOBAL_BRAID_PASS",check=control)
            except AssertionError as exc:record.update(status="RATIONALIZATION_FAILED",failure=str(exc)[:100])
            print(json.dumps(record,sort_keys=True),flush=True)
        if best<=4:break
    record={"status":"BOUNDED_SPARSE_SEARCH_COMPLETE","best_free_width":best,"union_columns":sorted(union),"rounds":records,
            "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(prefix+".json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in record.items() if k not in("rounds","union_columns")}),flush=True)


if __name__=="__main__":main()
