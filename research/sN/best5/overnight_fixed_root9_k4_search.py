"""Shared-parameter search on the parent's twelve K4 relaxation survivors.

Absolute values are imposed exactly by binary signs in a bounded MILP.
Every resulting rational candidate must satisfy all necessary equations
exactly and then pass the independent global network checker.
Negative bounded verdicts are only search diagnostics.
"""
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
import overnight_root9_equations as engine
from overnight_fixed_cross_verify import check as global_check


def main():
    start=time.monotonic();engine.initialize();a=engine.arithmetic
    survivors=json.loads(Path("overnight_root9_k4_probe.json").read_text())["survivors"];records=[];found=False
    base=json.loads(Path("overnight_fixed_cross_net9_17.json").read_text())
    for case,r in enumerate(survivors):
        zs=tuple(r["flats"]);ds=tuple(r["signs"]);equation,forms,offset=engine.case_data(zs,ds);n=offset[-1];m=len(forms);nv=n+2*m;B=16
        ri=[];ci=[];vv=[];lo=[];hi=[]
        def add(e,l,h):
            row=len(lo)
            for j,c in e.items():
                if c:ri.append(row);ci.append(j);vv.append(float(c))
            lo.append(l);hi.append(h)
        for q in range(49):
            e,rhs=equation(q);add({n+j:c for j,c in e.items()},float(rhs),float(rhs))
        for j,f in enumerate(forms):
            e={i:c for i,c in enumerate(f)if c};negative={i:-c for i,c in e.items()};y=n+j;s=n+m+j
            add(e|{y:-1},-np.inf,0);add(negative|{y:-1},-np.inf,0)
            add(negative|{y:1,s:2*B},-np.inf,2*B);add(e|{y:1,s:-2*B},-np.inf,0)
        lower=np.r_[np.full(n,-np.inf),np.zeros(m),np.zeros(m)];upper=np.r_[np.full(n,np.inf),np.full(m,B),np.ones(m)]
        for k,z in enumerate(zs):
            first=next(j for j,f in enumerate(forms)if any(f[offset[k]:offset[k+1]]));lower[n+m+first]=1
        A=coo_matrix((vv,(ri,ci)),shape=(len(lo),nv)).tocsc()
        result=milp(c=np.zeros(nv),integrality=np.r_[np.zeros(n+m,dtype=int),np.ones(m,dtype=int)],
                    bounds=Bounds(lower,upper),constraints=LinearConstraint(A,np.asarray(lo),np.asarray(hi)),options={"time_limit":20,"threads":1})
        record={"case":case,"flats":zs,"signs":ds,"variables":nv,"parameter_dimension":n,"solver_status":int(result.status),"message":result.message,"seconds":time.monotonic()-start}
        if result.x is not None:
            theta=[Q(float(c)).limit_denominator(1000000)for c in result.x[:n]];absolute=[abs(sum(a*b for a,b in zip(f,theta)))for f in forms]
            try:
                assert all(sum(c*absolute[j]for j,c in equation(q)[0].items())==equation(q)[1]for q in range(49))
                W=[]
                for k,z in enumerate(zs):W.append([sum(theta[offset[k]+j]*row[i]for j,row in enumerate(a.BASES[z]))for i in range(7)])
                trace=[Q(1-int(0 in S))-sum(d*max(sum(c*v for c,v in zip(w,a.VALUE[S])),Q(0))for d,w in zip(ds,W))for S in a.SETS[:-1]]
                rr=a.rref([list(a.VALUE[S])+[v]for S,v in zip(a.SETS[:-1],trace)]);assert len(rr)==7
                R=[row[-1]for row in rr];assert all(row[:7]==tuple(Q(int(i==j))for i in range(7))for j,row in enumerate(rr))
                net={"N":5,"first_layer":base["first_layer"],"second_layer":[list(map(str,R))+["1","-1"],list(map(str,[-c for c in R]))+["-1","1"]]+[list(map(str,w))+["0","0"]for w in W],"output":["1","-1"]+list(map(str,ds))}
                path=Path(f"overnight_fixed_root9_k4_case{case}_net.json");path.write_text(json.dumps(net,indent=2)+"\n")
                record["necessary_equations"]="EXACT_PASS"
                try:
                    receipt=global_check(path);Path(f"overnight_fixed_root9_k4_case{case}_check.json").write_text(json.dumps(receipt,sort_keys=True,indent=2)+"\n")
                    record["global_check"]="EXACT_PASS";found=True
                except AssertionError as exc:record.update(global_check="FAILED",failure=str(exc)[:500])
            except AssertionError as exc:record.update(necessary_equations="RATIONALIZATION_FAILED",failure=str(exc)[:500])
        records.append(record);print(json.dumps(record,sort_keys=True),flush=True)
        if found:break
    report={"status":"EXACT_NINE_SIX_CONSTRUCTION"if found else"BOUNDED_SURVIVOR_SEARCH_COMPLETE","records":records,"absolute_bound":16,
            "strict_margin":0,"scope":"Twelve sampled flat/sign patterns only; no negative theorem","seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_root9_k4_search.json").write_text(json.dumps(report,sort_keys=True,indent=2)+"\n");print(json.dumps({k:v for k,v in report.items()if k!="records"}),flush=True)


if __name__=="__main__":main()
