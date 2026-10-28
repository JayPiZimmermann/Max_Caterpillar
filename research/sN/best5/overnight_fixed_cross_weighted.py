"""Positive sparse search favoring outer forms active at more top-tie cells.
The finite dictionary and coefficient bounds are search choices, not exclusions.
"""
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import hstack
from overnight_fixed_cross_sparse import matrices,exact_check


def main():
    start=time.monotonic();edges,allW,allA,target=matrices(3)
    S=[frozenset(c) for n in(3,4) for c in itertools.combinations(range(5),n)];ix={s:i for i,s in enumerate(S)}
    V=np.asarray([[int(i in s and j not in s) for i,j in edges] for s in S]).T
    zeros=allW@V==0;cover=np.zeros(len(allW),dtype=np.int64)
    for U in S[:10]:
        for o in range(5):
            if o not in U:cover+=zeros[:,ix[U]] & zeros[:,ix[U|{o}]]
    z=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")
    selected=set(np.argsort(abs(z["weights"][7:]))[::-1][:2000]);selected.update(np.flatnonzero(cover>=8))
    selected.update(np.flatnonzero(np.max(abs(allW),axis=1)==1))
    take=np.asarray(sorted(selected));W=allW[take];A=hstack([allA[:,:7],allA[:,7+take]],format="csc");m=len(W)
    B=hstack([A[:,:7],A[:,7:],-A[:,7:]],format="csc");random=np.random.default_rng(817);best=10000;union=set();records=[]
    for iteration in range(24):
        power=iteration%3;prices=1/cover[take].astype(float)**power
        if iteration>=3:prices*=np.exp(random.uniform(-1.5,1.5,m))
        result=linprog(np.r_[np.zeros(7),prices,prices],A_eq=B,b_eq=target,
                       bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs",options={"time_limit":15})
        r={"iteration":iteration,"solver_status":result.status,"seconds":time.monotonic()-start};records.append(r)
        if result.x is None:continue
        values=result.x[7:7+m]-result.x[7+m:];support=np.flatnonzero(abs(values)>1e-7);union.update(int(take[j]) for j in support)
        r["support"]=len(support)
        if len(support)<best:
            R=[Q(float(c)).limit_denominator(1000000) for c in result.x[:7]]
            D=[Q(float(values[j])).limit_denominator(1000000) for j in support];WW=[tuple(map(Q,map(int,W[j]))) for j in support]
            try:
                r.update(status="EXACT_GLOBAL_BRAID_PASS",check=exact_check(edges,WW,R,D));best=len(support)
                candidate={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,row)) for row in WW],"output":list(map(str,D))}
                Path("overnight_fixed_cross_weighted_candidate.json").write_text(json.dumps(candidate,indent=2)+"\n")
            except AssertionError as exc:r.update(status="RATIONALIZATION_FAILED",failure=str(exc)[:200])
            print(json.dumps(r,sort_keys=True),flush=True)
        if best<=4:break
    result={"status":"WEIGHTED_POSITIVE_SEARCH_COMPLETE","dictionary_size":m,"best_free_width":best,
            "union_columns":sorted(union),"rounds":records,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_weighted.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in("rounds","union_columns")}),flush=True)


if __name__=="__main__":main()
