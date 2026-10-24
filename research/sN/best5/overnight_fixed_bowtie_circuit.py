"""Exact circuit-cut pruning of the bowtie K=3 relaxation survivors.

Floating LPs only choose valid circuit inequalities. Final exclusion is
accepted solely from exact rational Farkas verification. Missing cuts or
numerical tolerances can produce only extra survivors.
"""
import argparse
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import exact_lp
import fastlp
from overnight_fixed_bowtie_k3 import problem
from overnight_fixed_circuits import inequalities


def check(p):
    if p is None:return False,0
    n,offsets,rows=p
    forms=sorted({f for e,r in rows for f in e});m=len(forms)
    E=[[-r]+[e.get(f,Q(0)) for f in forms] for e,r in rows]
    nonnegative=[[Q(0)]+[Q(int(i==j)) for j in range(m)] for i in range(m)]
    cuts=inequalities(forms,offsets,4)
    if not cuts:return exact_lp.feasible(E,nonnegative,m),0
    floatcuts=np.asarray([[float(x) for x in row[1:]] for row in cuts])
    active=[];used=set()
    for step in range(100):
        I=[cuts[i] for i in active]
        allrows=E+I
        a=np.asarray([[float(c) for c in row[1:]] for row in allrows])
        rhs=-np.asarray([float(row[0]) for row in allrows]);hi=np.full(len(allrows),np.inf);hi[:len(E)]=rhs[:len(E)]
        name,y,_=fastlp.solve(np.zeros(m),a,rhs,hi,np.zeros(m),np.full(m,np.inf))
        if name!="Optimal":
            return exact_lp.feasible(E,nonnegative+I,m),len(active)
        violations=floatcuts@y
        new=[int(i) for i in np.argsort(violations) if violations[i]<-1e-8 and int(i) not in used][:40]
        if not new:return True,len(active)
        active+=new;used.update(new)
    return True,len(active)


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=1200)
    ap.add_argument("--rays",action="store_true");args=ap.parse_args()
    def timeout(*_):raise TimeoutError("declared budget")
    signal.signal(signal.SIGALRM,timeout);signal.alarm(args.budget)
    outpath=Path("overnight_fixed_bowtie_k3_raycut.jsonl" if args.rays else "overnight_fixed_bowtie_k3_circuit.jsonl");done=set()
    if outpath.exists():
        for line in outpath.read_text().splitlines():
            r=json.loads(line);done.add((tuple(r["flats"]),tuple(r["signs"])))
    started=time.monotonic();processed=survived=0
    try:
        inputpath="overnight_fixed_bowtie_k3_circuit.jsonl" if args.rays else "overnight_fixed_bowtie_k3_relax.jsonl"
        with open(inputpath) as inp,outpath.open("a") as out:
            for line in inp:
                r=json.loads(line)
                if r["status"]!="SURVIVOR":continue
                zs=tuple(r["flats"]);ds=tuple(r["signs"])
                if (zs,ds) in done:continue
                if args.rays:
                    from overnight_fixed_bowtie_ray import ray_problem
                    p=ray_problem(zs,ds)
                else:p=problem(zs,ds)
                found,ncuts=check(p)
                row={"flats":zs,"signs":ds,"status":"SURVIVOR" if found else "EXCLUDED","cuts":ncuts}
                out.write(json.dumps(row,separators=(",",":"))+"\n");out.flush()
                processed+=1;survived+=found
                if processed%100==0:print(json.dumps({"processed":processed,"survivors":survived,"lp":exact_lp.STATS,"seconds":time.monotonic()-started}),flush=True)
    except TimeoutError:
        print(json.dumps({"status":"BUDGET_EXHAUSTED","processed":processed,"survivors":survived,"seconds":time.monotonic()-started}),flush=True)
        raise SystemExit(124)
    print(json.dumps({"status":"COMPLETE","processed":processed,"survivors":survived,"lp":exact_lp.STATS,"seconds":time.monotonic()-started}),flush=True)


if __name__=="__main__":main()
