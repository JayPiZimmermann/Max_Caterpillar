"""Interior-point sparse extraction from the full finite dictionary.
Positive search only; all resulting rational coefficients are checked exactly.
"""
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
    start=time.monotonic();edges,W,A,target=matrices(3);m=len(W)
    B=hstack([A[:,:7],A[:,7:],-A[:,7:]],format="csc")
    print("FULL_DICTIONARY_IPM_START",flush=True)
    result=linprog(np.r_[np.zeros(7),np.ones(2*m)],A_eq=B,b_eq=target,
                   bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs-ipm",
                   options={"time_limit":300,"presolve":True})
    record={"status":"NO_CANDIDATE","solver_status":result.status,"message":result.message,
            "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if result.x is not None:
        values=result.x[7:7+m]-result.x[7+m:];support=np.flatnonzero(abs(values)>1e-7)
        R=[Q(float(c)).limit_denominator(1000000) for c in result.x[:7]]
        D=[Q(float(values[j])).limit_denominator(1000000) for j in support];WW=[tuple(map(Q,map(int,W[j]))) for j in support]
        candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row)) for row in WW],"output":list(map(str,D))}
        Path("overnight_fixed_cross_ipm_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
        record.update(support_size=len(support),objective=result.fun)
        try:record.update(status="EXACT_GLOBAL_BRAID_PASS",check=exact_check(edges,WW,R,D))
        except AssertionError as exc:record.update(status="RATIONALIZATION_FAILED",failure=str(exc)[:500])
    Path("overnight_fixed_cross_ipm.json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
    print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
