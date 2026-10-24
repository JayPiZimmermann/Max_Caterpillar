"""Bounded exact necessary-condition search for three bowtie neurons.

Stage relax: independent absolute-value symbols >=0, all locality equations.
Every exclusion is an exact rational Farkas proof via exact_lp. Survivors
are only candidates for the stricter common-linear-parameter search.
Stage dfs: shared real flat coordinates, closed canonical sign chambers.
This script preserves all archived data and appends per-sign checkpoints.
"""
import argparse
import functools
import itertools
import json
import signal
import time
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import exact_lp
from k2b import reduce_constraints
from overnight_fixed_bowtie import VR,ALL,REL,LOCS
from overnight_fixed_k2 import canonical

INV=json.loads(Path("overnight_fixed_bowtie_inventory.json").read_text())
FLATS={int(z):row for z,row in INV["flats"].items()}


@functools.lru_cache(None)
def data(z):
    basis=[[Q(c) for c in row] for row in FLATS[z]["basis"]]
    vals={S:tuple(sum(a*b for a,b in zip(VR[S],v)) for v in basis) for S in ALL}
    qs={}
    for U in ALL:
        if len(U)<3 or any(vals[U]):continue
        expr={}
        for W in ALL:
            if W<U:
                f,c=canonical(vals[W])
                if f is not None:expr[f]=expr.get(f,Q(0))+c*(-1)**(len(U)-len(W))
        qs[U]={f:c for f,c in expr.items() if c}
    return len(basis),qs


def problem(zs,ds):
    covers=[{i for i in range(20) if FLATS[z]["cover"]>>i&1} for z in zs]
    ok,cons=reduce_constraints(covers,ds)
    if not ok:return None
    for i,U in enumerate(S for S in REL if len(S)==4):
        ks=[k for k,z in enumerate(zs) if FLATS[z]["cover"]>>(20+i)&1]
        if not ks:return None
        cons.append((U,{k:Q(ds[k]) for k in ks},Q(-1)))
    cons.append((frozenset(range(5)),{k:Q(ds[k]) for k in range(len(zs))},Q(1)))
    offsets=[0]
    for z in zs:offsets.append(offsets[-1]+data(z)[0])
    n=offsets[-1];rows=[]
    for U,cs,rhs in cons:
        expr={}
        for k,c in cs.items():
            for f,a in data(zs[k])[1].get(U,{}).items():
                lifted=tuple([Q(0)]*offsets[k]+list(f)+[Q(0)]*(n-offsets[k+1]))
                expr[lifted]=expr.get(lifted,Q(0))+c*a
        expr={f:c for f,c in expr.items() if c}
        if (rhs>0 and all(c<=0 for c in expr.values())) or (rhs<0 and all(c>=0 for c in expr.values())):
            return None
        rows.append((expr,2*rhs))
    return n,offsets,rows


def relaxation(p):
    if p is None:return False
    n,offsets,rows=p
    forms=sorted({f for e,r in rows for f in e});m=len(forms)
    E=[[-r]+[e.get(f,Q(0)) for f in forms] for e,r in rows]
    I=[[Q(0)]+[Q(int(i==j)) for j in range(m)] for i in range(m)]
    return exact_lp.feasible(E,I,m)


def dfs(p):
    if p is None:return False,0
    n,offsets,rows=p
    forms=sorted({f for e,r in rows for f in e});signs={};I=[];nodes=[0]
    for k in range(len(offsets)-1):
        f=next((f for f in forms if any(f[offsets[k]:offsets[k+1]])),None)
        if f is not None:signs[f]=1;I.append([Q(0)]+list(f))
    def rec(signs,pending,E,I):
        nodes[0]+=1
        left=[];EE=list(E)
        for expr,rhs in pending:
            if all(f in signs for f in expr):
                row=[-rhs]+[sum(c*signs[f]*f[j] for f,c in expr.items()) for j in range(n)]
                if not any(row[1:]):
                    if row[0]:return False
                    continue
                EE.append(row)
            else:left.append((expr,rhs))
        if not exact_lp.feasible(EE,I,n):return False
        if not left:return True
        expr,rhs=min(left,key=lambda er:(sum(f not in signs for f in er[0]),len(er[0])))
        f=max((f for f in expr if f not in signs),key=lambda f:sum(f in e for e,r in left))
        for s in (1,-1):
            ss=dict(signs);ss[f]=s
            if rec(ss,left,EE,I+[[Q(0)]+[s*x for x in f]]):return True
        return False
    return rec(signs,rows,[],I),nodes[0]


def triples():
    by=defaultdict(list)
    for z,row in FLATS.items():by[row["cover"]].append(z)
    result=set()
    for ms in INV["triple_masks"]:
        for zs in itertools.product(*(by[m] for m in ms)):result.add(tuple(sorted(zs)))
    return sorted(result)


def main():
    ap=argparse.ArgumentParser();ap.add_argument("stage",choices=["relax","dfs"])
    ap.add_argument("--budget",type=int,default=1200);ap.add_argument("--limit",type=int,default=1000000)
    args=ap.parse_args()
    def timeout(*_):raise TimeoutError("declared wall-clock budget")
    signal.signal(signal.SIGALRM,timeout);signal.alarm(args.budget)
    started=time.monotonic();outpath=Path("overnight_fixed_bowtie_k3_"+args.stage+".jsonl")
    done=set()
    if outpath.exists():
        for line in outpath.read_text().splitlines():
            rec=json.loads(line);done.add((tuple(rec["flats"]),tuple(rec["signs"])))
    todo=[]
    if args.stage=="relax":
        for zs in triples():
            for ds in itertools.product((1,-1),repeat=3):todo.append((zs,ds))
    else:
        for line in Path("overnight_fixed_bowtie_k3_relax.jsonl").read_text().splitlines():
            rec=json.loads(line)
            if rec["status"]=="SURVIVOR":todo.append((tuple(rec["flats"]),tuple(rec["signs"])))
    processed=survived=0
    try:
        with outpath.open("a") as out:
            for zs,ds in todo:
                if (zs,ds) in done:continue
                if processed>=args.limit:break
                p=problem(zs,ds)
                if args.stage=="relax":found=relaxation(p);nodes=0
                else:found,nodes=dfs(p)
                rec={"flats":zs,"signs":ds,"status":"SURVIVOR" if found else "EXCLUDED","nodes":nodes}
                out.write(json.dumps(rec,separators=(",",":"))+"\n");out.flush()
                processed+=1;survived+=found
                if processed%1000==0:print(json.dumps({"processed":processed,"new_survivors":survived,"lp":exact_lp.STATS,"seconds":time.monotonic()-started}),flush=True)
    except TimeoutError:
        print(json.dumps({"status":"BUDGET_EXHAUSTED","processed":processed,"new_survivors":survived,"seconds":time.monotonic()-started}),flush=True)
        raise SystemExit(124)
    print(json.dumps({"status":"BATCH_COMPLETE","processed":processed,"new_survivors":survived,"total_candidates":len(todo),"lp":exact_lp.STATS,"seconds":time.monotonic()-started}),flush=True)


if __name__=="__main__":main()
