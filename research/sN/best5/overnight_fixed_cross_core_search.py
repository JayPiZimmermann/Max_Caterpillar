"""Find different four-neuron cancellation cores and refine them continuously."""
import hashlib
import itertools
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import hstack
from overnight_fixed_cross_sparse import matrices,exact_check
from overnight_fixed_cross_pattern import refine


def main():
    start=time.monotonic();edges,allW,allA,target=matrices(3)
    S=[frozenset(c) for n in(3,4) for c in itertools.combinations(range(5),n)];ix={s:i for i,s in enumerate(S)}
    V=np.asarray([[int(i in s and j not in s) for i,j in edges]for s in S]).T;zero=allW@V==0
    cover=sum((zero[:,ix[u]]&zero[:,ix[u|{o}]]).astype(int) for u in S[:10]for o in range(5)if o not in u)
    z=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz");select=set(np.argsort(abs(z["weights"][7:]))[::-1][:2000])
    select.update(np.flatnonzero(cover>=8));select.update(np.flatnonzero(np.max(abs(allW),axis=1)==1));take=np.asarray(sorted(select))
    W=allW[take];A=hstack([allA[:,:7],allA[:,7+take]],format="csc");m=len(W);B=hstack([A[:,:7],A[:,7:],-A[:,7:]],format="csc")
    crosses=A[:-30,7:].getnnz(axis=0)>0;random=np.random.default_rng(1901);seen=set();records=[];found=False
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")));signal.alarm(300)
    try:
        for iteration in range(100):
            prices=np.exp(random.uniform(-2,2,m))/cover[take].astype(float)**(iteration%3)
            # Favor plans in which the nonlinear curvature is carried by
            # few forms; the correction terms may then be discarded in
            # the subsequent continuous-coefficient feasibility test.
            if iteration%4==3:prices[crosses]*=5
            result=linprog(np.r_[np.zeros(7),prices,prices],A_eq=B,b_eq=target,
                           bounds=[(None,None)]*7+[(0,None)]*(2*m),method="highs",options={"time_limit":10})
            if result.x is None:continue
            values=result.x[7:7+m]-result.x[7+m:];core=np.flatnonzero((abs(values)>1e-7)&crosses)
            if not(1<=len(core)<=4):continue
            D=[Q(float(values[j])).limit_denominator(1000000) for j in core]
            key=tuple((int(take[j]),str(d/abs(D[0])))for j,d in zip(core,D))
            if key in seen:continue
            seen.add(key);candidate={"first_layer_edges":edges,"outer_forms":[list(map(str,W[j]))for j in core],"output":list(map(str,D))}
            try:r=refine(candidate,list(range(len(core))))
            except AssertionError:
                records.append({"iteration":iteration,"status":"ROUNDING_OR_PATTERN_REJECTED","key":key});continue
            records.append({"iteration":iteration,"status":r["solver_status"],"key":key})
            print(json.dumps({"iteration":iteration,"cores":len(seen),"free_width":len(core),"status":r["solver_status"],"seconds":time.monotonic()-start}),flush=True)
            if "candidate" in r:
                Path("overnight_fixed_cross_core_search_candidate.json").write_text(json.dumps(r["candidate"],indent=2)+"\n");found=True;break
    except TimeoutError:print("DECLARED_BUDGET_REACHED",flush=True)
    finally:signal.alarm(0)
    result={"status":"EXACT_FOUR_FREE_CANDIDATE" if found else "CORE_PATTERN_BATCH_COMPLETE","records":records,
            "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_core_search.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items()if k!="records"}),flush=True)


if __name__=="__main__":main()
