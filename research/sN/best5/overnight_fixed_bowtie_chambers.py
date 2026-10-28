"""Full-dimensional chamber refinement for difficult closed-sign searches.

At every point of a finite central hyperplane arrangement, some full-
dimensional sign chamber has that point in its closure. Hence it is enough
to solve the target equations in closures of sign chambers whose strict
sign inequalities alone are feasible. Strict signs are NEVER imposed
together with the target equations: boundary solutions remain covered.
This is currently a search instrument, not an independently checked
certificate. Infeasible strict systems use exact rational Farkas checks.
"""
import argparse
import functools
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import exact_lp
from overnight_fixed_bowtie_ray import ray_problem


@functools.lru_cache(maxsize=50000)
def strict_block(rows):
    if not rows:return True
    return exact_lp.feasible([],[[Q(-1)]+list(r) for r in rows],len(rows[0]))


def chamber_dfs(p):
    if p is None:return False,{"nodes":0,"strict_prunes":0}
    n,offsets,rows=p
    forms=sorted({f for e,r in rows for f in e});signs={};I=[];stats={"nodes":0,"strict_prunes":0}
    for k in range(len(offsets)-1):
        f=next((f for f in forms if any(f[offsets[k]:offsets[k+1]])),None)
        if f is not None:signs[f]=1;I.append([Q(0)]+list(f))
    def rec(signs,pending,E,I):
        stats["nodes"]+=1;EE=list(E);left=[]
        for expr,rhs in pending:
            if all(f in signs for f in expr):
                row=[-rhs]+[sum(c*signs[f]*f[j] for f,c in expr.items()) for j in range(n)]
                if not any(row[1:]):
                    if row[0]:return False
                    continue
                EE.append(row)
            else:left.append((expr,rhs))
        if not exact_lp.feasible(EE,I,n):return False
        for k in range(len(offsets)-1):
            local=tuple(sorted(tuple(signs[f]*x for x in f[offsets[k]:offsets[k+1]]) for f in signs if any(f[offsets[k]:offsets[k+1]])))
            if not strict_block(local):stats["strict_prunes"]+=1;return False
        if not left:return True
        expr,rhs=min(left,key=lambda er:(sum(f not in signs for f in er[0]),len(er[0])))
        f=max((f for f in expr if f not in signs),key=lambda f:sum(f in e for e,r in left))
        for s in (1,-1):
            ss=dict(signs);ss[f]=s
            if rec(ss,left,EE,I+[[Q(0)]+[s*x for x in f]]):return True
        return False
    return rec(signs,rows,[],I),stats


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=120)
    ap.add_argument("--flats",default="23750,24007,32510");ap.add_argument("--signs",default="-1,1,1")
    args=ap.parse_args()
    def timeout(*_):raise TimeoutError("declared budget")
    signal.signal(signal.SIGALRM,timeout);signal.alarm(args.budget)
    zs=tuple(map(int,args.flats.split(',')));ds=tuple(map(int,args.signs.split(',')));t=time.monotonic()
    try:
        found,stats=chamber_dfs(ray_problem(zs,ds))
        result={"status":"SURVIVOR" if found else "CHAMBER_EXCLUDED","stats":stats}
    except TimeoutError:result={"status":"TIMEOUT"}
    result.update({"flats":zs,"signs":ds,"seconds":time.monotonic()-t,"lp":exact_lp.STATS,
                   "trust":"exact arithmetic search plus full-dimensional closure argument; no independent checker yet"})
    with open("overnight_fixed_bowtie_k3_chambers.jsonl","a") as out:out.write(json.dumps(result,separators=(",",":"))+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
