"""Bounded full-real necessary-condition search for a natural8 (8,6) net.

Four free preactivations in the six-feature span, plus a free remainder
in that same span. Covers all vanishing flats and output signs. Exact
LP exclusions are research evidence until an independent certificate
is produced. A surviving necessary system is not a global construction.
"""
import argparse
import functools
import itertools
import json
import math
import signal
import time
from collections import Counter,defaultdict
from fractions import Fraction as Q
from pathlib import Path
import exact_lp
from flats_loc import nullspace
from k2b import reduce_constraints
from overnight_fixed_k2 import canonical
from overnight_fixed_bowtie_k3 import dfs
from overnight_fixed_bowtie_circuit import check as circuit_check

SETS=[frozenset(c) for k in range(1,6) for c in itertools.combinations(range(5),k)]
REL=[S for S in SETS if len(S) in (3,4)]
INV=json.loads(Path("overnight_fixed_natural8_inventory.json").read_text())
FLATS={int(z):v for z,v in INV["flats"].items()}
def vr(S):
    x=[Q(int(i in S)) for i in range(5)];u,v,s,t=[x[i]-x[0] for i in range(1,5)]
    return tuple(max(a,0) for a in (u,v,u-v,s,t,s-t))
VR={S:vr(S) for S in SETS};ANN=nullspace([[VR[S][i] for S in SETS[:-1]] for i in range(6)],30)
TARGET=[2*sum(a*(1-int(0 in S)) for a,S in zip(row,SETS[:-1])) for row in ANN]
assert len(ANN)==24


@functools.lru_cache(None)
def data(z):
    B=[[Q(c) for c in b] for b in FLATS[z]["basis"]]
    vv={S:tuple(sum(a*b for a,b in zip(VR[S],v)) for v in B) for S in SETS};cubes={};rays=[]
    for U in SETS:
        if len(U)<3 or any(vv[U]):continue
        e={}
        for S in SETS:
            if not S<U:continue
            f,c=canonical(vv[S])
            if f is not None:e[f]=e.get(f,Q(0))+c*(-1)**(len(U)-len(S))
        cubes[U]={f:c for f,c in e.items() if c}
    for row in ANN:
        e={}
        for a,S in zip(row,SETS[:-1]):
            f,c=canonical(vv[S])
            if a and f is not None:e[f]=e.get(f,Q(0))+a*c
        rays.append({f:c for f,c in e.items() if c})
    return len(B),cubes,rays


def problem(zs,ds):
    covers=[{i for i in range(20) if FLATS[z]["cover"]>>i&1} for z in zs]
    ok,cons=reduce_constraints(covers,ds)
    if not ok:return None
    for i,U in enumerate(S for S in REL if len(S)==4):
        ks=[k for k,z in enumerate(zs) if FLATS[z]["cover"]>>(20+i)&1]
        if not ks:return None
        cons.append((U,{k:Q(ds[k]) for k in ks},Q(-1)))
    cons.append((frozenset(range(5)),{k:Q(d) for k,d in enumerate(ds)},Q(1)))
    offsets=[0]
    for z in zs:offsets.append(offsets[-1]+data(z)[0])
    n=offsets[-1];rows=[]
    def combine(parts,rhs):
        e={}
        for k,cs,c in parts:
            for f,a in cs.items():
                lifted=tuple([Q(0)]*offsets[k]+list(f)+[Q(0)]*(n-offsets[k+1]))
                e[lifted]=e.get(lifted,Q(0))+c*a
        e={f:c for f,c in e.items() if c}
        if rhs and all(c*rhs<=0 for c in e.values()):return False
        rows.append((e,rhs));return True
    for U,coeff,rhs in cons:
        if not combine([(k,data(zs[k])[1].get(U,{}),c) for k,c in coeff.items()],2*rhs):return None
    for q,rhs in enumerate(TARGET):
        if not combine([(k,data(z)[2][q],Q(d)) for k,(z,d) in enumerate(zip(zs,ds))],rhs):return None
    return n,offsets,rows


def quadruples():
    pairs=defaultdict(list);zs=sorted(FLATS);full=(1<<25)-1
    for i,z in enumerate(zs):
        for zz in zs[i:]:pairs[FLATS[z]["cover"]|FLATS[zz]["cover"]].append((z,zz))
    answer=[]
    for a,pp in pairs.items():
        for b,qq in pairs.items():
            if a|b!=full:continue
            for z1,z2 in pp:
                for z3,z4 in qq:
                    if z2<=z3:answer.append((z1,z2,z3,z4))
    answer.sort();assert len(set(answer))==len(answer)
    assert sum(math.factorial(4)//math.prod(math.factorial(c) for c in Counter(z).values()) for z in answer)==INV["covering_ordered_quadruples"]
    return answer


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--stage",choices=["cone","sign"],default="cone")
    ap.add_argument("--budget",type=int,default=1200);ap.add_argument("--case-budget",type=int,default=60);args=ap.parse_args()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")))
    start=time.monotonic();path=Path("overnight_fixed_natural8_k4_"+args.stage+".jsonl");done=set()
    if path.exists():
        for line in path.read_text().splitlines():
            r=json.loads(line)
            if r["status"]!="TIMEOUT":done.add((tuple(r["flats"]),tuple(r["signs"])))
    if args.stage=="cone":todo=[(z,d) for z in quadruples() for d in itertools.product((1,-1),repeat=4)]
    else:
        todo=[]
        for line in Path("overnight_fixed_natural8_k4_cone.jsonl").read_text().splitlines():
            r=json.loads(line)
            if r["status"]=="SURVIVOR":todo.append((tuple(r["flats"]),tuple(r["signs"])))
    counts=Counter();processed=0
    with path.open("a") as out:
        for zs,ds in todo:
            if (zs,ds) in done:continue
            remain=args.budget-(time.monotonic()-start)
            if remain<=0:break
            signal.alarm(max(1,min(args.case_budget,int(remain))))
            try:
                p=problem(zs,ds)
                found,nodes=circuit_check(p) if args.stage=="cone" else dfs(p)
                status="SURVIVOR" if found else "EXCLUDED"
            except TimeoutError:status="TIMEOUT";nodes=None
            finally:signal.alarm(0)
            out.write(json.dumps({"flats":zs,"signs":ds,"status":status,"nodes_or_cuts":nodes},separators=(",",":"))+"\n");out.flush()
            counts[status]+=1;processed+=1
            if processed%1000==0:print(json.dumps({"processed":processed,"counts":counts,"seconds":time.monotonic()-start}),flush=True)
    print(json.dumps({"status":"BATCH_COMPLETE","processed":processed,"total_cases":len(todo),"counts":counts,"seconds":time.monotonic()-start}),flush=True)


if __name__=="__main__":main()
