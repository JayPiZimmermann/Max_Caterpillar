"""Sparse candidate search restricted to the strongest numerical dictionary columns."""
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
    start=time.monotonic();orientation=2;edges,allW,allA,target=matrices(orientation)
    z=np.load("overnight_fixed_cross_dictionary_2_orientation2_candidate.npz")
    order=np.argsort(abs(z["weights"][7:]))[::-1]
    for limit in (2000,5000,10000):
        take=np.sort(order[:limit]);W=allW[take];A=hstack([allA[:,:7],allA[:,7+take]],format="csc");m=len(W)
        B=hstack([A[:,:7],A[:,7:],-A[:,7:]],format="csc")
        result=linprog(np.r_[np.zeros(7),np.ones(2*m)],A_eq=B,b_eq=target,
                       bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs",options={"time_limit":45})
        record={"limit":limit,"status":"NO_CANDIDATE","solver_status":result.status,"message":result.message,
                "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
        if result.x is not None:
            values=result.x[7:7+m]-result.x[7+m:];support=np.flatnonzero(abs(values)>1e-7)
            R=[Q(float(c)).limit_denominator(1000000) for c in result.x[:7]]
            D=[Q(float(values[j])).limit_denominator(1000000) for j in support]
            WW=[tuple(map(Q,map(int,W[j]))) for j in support]
            candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row)) for row in WW],"output":list(map(str,D))}
            prefix=f"overnight_fixed_cross_subset_{limit}"
            Path(prefix+"_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
            record.update(support_size=len(support),objective=result.fun)
            try:record.update(status="EXACT_GLOBAL_BRAID_CANDIDATE_PASS",check=exact_check(edges,WW,R,D))
            except AssertionError as exc:record.update(status="RATIONALIZATION_FAILED",failure=str(exc)[:500])
        Path(f"overnight_fixed_cross_subset_{limit}.json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
        print(json.dumps(record,sort_keys=True),flush=True)
        if record["status"]=="EXACT_GLOBAL_BRAID_CANDIDATE_PASS":break


if __name__=="__main__":main()
