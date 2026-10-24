"""Strengthen fixed-layer K=3 equations by eliminating the free remainder.

Thirty nontrivial Boolean rays give a30x8 feature matrix. Its22-dimensional
left kernel eliminates the eight free-remainder coefficients exactly.
The resulting equations concern only absolute preactivation values and
retain closed sign chambers, so an exact exclusion is sound on boundaries.
"""
import argparse
import functools
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import exact_lp
from flats_loc import nullspace
from overnight_fixed_bowtie import VR,ALL
from overnight_fixed_bowtie_k3 import FLATS,problem,relaxation,dfs
from overnight_fixed_k2 import canonical

RAYS=[S for S in ALL if len(S)<5]
ANN=nullspace([[VR[S][i] for S in RAYS] for i in range(8)],30)
assert len(ANN)==22
TARGET=[2*sum(a*(1-int(1 in S)) for a,S in zip(row,RAYS)) for row in ANN]


@functools.lru_cache(None)
def ray_data(z):
    B=[[Q(c) for c in b] for b in FLATS[z]["basis"]]
    vals={S:canonical(tuple(sum(a*b for a,b in zip(VR[S],v)) for v in B)) for S in RAYS}
    result=[]
    for row in ANN:
        expr={}
        for c,S in zip(row,RAYS):
            f,scale=vals[S]
            if c and f is not None:expr[f]=expr.get(f,Q(0))+c*scale
        result.append({f:c for f,c in expr.items() if c})
    return result


def ray_problem(zs,ds):
    p=problem(zs,ds)
    if p is None:return None
    n,offsets,rows=p;rows=list(rows)
    for q,rhs in enumerate(TARGET):
        expr={}
        for k,(z,d) in enumerate(zip(zs,ds)):
            for f,c in ray_data(z)[q].items():
                lifted=tuple([Q(0)]*offsets[k]+list(f)+[Q(0)]*(n-offsets[k+1]))
                expr[lifted]=expr.get(lifted,Q(0))+d*c
        expr={f:c for f,c in expr.items() if c}
        if (rhs>0 and all(c<=0 for c in expr.values())) or (rhs<0 and all(c>=0 for c in expr.values())):return None
        rows.append((expr,rhs))
    return n,offsets,rows


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=1200)
    ap.add_argument("--case-budget",type=int,default=60);ap.add_argument("--limit",type=int,default=1000000)
    ap.add_argument("--only-raycut",action="store_true")
    args=ap.parse_args()
    def timeout(*_):raise TimeoutError("case budget")
    signal.signal(signal.SIGALRM,timeout)
    path=Path("overnight_fixed_bowtie_k3_ray.jsonl");done=set()
    if path.exists():
        for line in path.read_text().splitlines():
            r=json.loads(line)
            if r["status"]!="TIMEOUT":done.add((tuple(r["flats"]),tuple(r["signs"])))
    source="overnight_fixed_bowtie_k3_raycut.jsonl" if args.only_raycut else "overnight_fixed_bowtie_k3_circuit.jsonl"
    text=Path(source).read_text();lines=text.splitlines()
    if not text.endswith("\n"):lines=lines[:-1]
    started=time.monotonic();counts={};processed=0
    with path.open("a") as out:
        for line in lines:
            rec=json.loads(line)
            if rec["status"]!="SURVIVOR":continue
            zs=tuple(rec["flats"]);ds=tuple(rec["signs"])
            if (zs,ds) in done:continue
            if processed>=args.limit or time.monotonic()-started>=args.budget:break
            t=time.monotonic();signal.alarm(min(args.case_budget,max(1,int(args.budget-(t-started)))))
            try:
                p=ray_problem(zs,ds)
                if not relaxation(p):status="RAY_CONE_EXCLUDED";nodes=0
                else:
                    found,nodes=dfs(p);status="SURVIVOR" if found else "RAY_SIGN_EXCLUDED"
            except TimeoutError:status="TIMEOUT";nodes=None
            finally:signal.alarm(0)
            row={"flats":zs,"signs":ds,"status":status,"nodes":nodes,"seconds":time.monotonic()-t}
            out.write(json.dumps(row,separators=(",",":"))+"\n");out.flush()
            counts[status]=counts.get(status,0)+1;processed+=1
            if processed%50==0 or status in ("SURVIVOR","TIMEOUT"):print(json.dumps({"processed":processed,"counts":counts,"latest":row,"seconds":time.monotonic()-started}),flush=True)
    print(json.dumps({"status":"BATCH_COMPLETE","processed":processed,"counts":counts,"seconds":time.monotonic()-started}),flush=True)


if __name__=="__main__":main()
