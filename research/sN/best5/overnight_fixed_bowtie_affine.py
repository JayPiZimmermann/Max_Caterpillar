"""Exact affine reduction of absolute-value sign searches.

Completed linear equalities are eliminated before choosing the next sign.
Forms that become constant or proportional modulo those equalities share
their forced signs or one common closed branch. This preserves all
boundary solutions and avoids exponential duplication of zero faces.
Search exclusions still need an independent proof-tree checker.
"""
import argparse
import functools
import json
import signal
import time
from fractions import Fraction as Q
import exact_lp
from k2_exact import solve_eq
from overnight_fixed_bowtie_ray import ray_problem


@functools.lru_cache(maxsize=5000)
def affine(E,n):
    if not E:return [Q(0)]*n,[[Q(int(i==j)) for i in range(n)] for j in range(n)]
    return solve_eq(E,n)


def affine_dfs(p):
    if p is None:return False,{"nodes":0,"forced_signs":0,"group_branches":0}
    n,offsets,rows=p
    forms=sorted({f for e,r in rows for f in e});signs={};I=[]
    stats={"nodes":0,"forced_signs":0,"group_branches":0}
    for k in range(len(offsets)-1):
        f=next((f for f in forms if any(f[offsets[k]:offsets[k+1]])),None)
        if f is not None:signs[f]=1;I.append([Q(0)]+list(f))

    def rec(signs,pending,E,I):
        stats["nodes"]+=1
        signs=dict(signs);E=list(E)
        while True:
            left=[]
            for expr,rhs in pending:
                if all(f in signs for f in expr):
                    row=[-rhs]+[sum(c*signs[f]*f[j] for f,c in expr.items()) for j in range(n)]
                    if not any(row[1:]):
                        if row[0]:return False
                        continue
                    E.append(row)
                else:left.append((expr,rhs))
            pending=left
            sol=affine(tuple(tuple(row) for row in E),n)
            if sol is None:return False
            x0,basis=sol;groups={};which={};changed=False
            for f in forms:
                reduced=tuple([sum(a*b for a,b in zip(f,x0))]+[sum(a*b for a,b in zip(f,v)) for v in basis])
                if not any(reduced[1:]):
                    value=reduced[0]
                    if f in signs:
                        if value*signs[f]<0:return False
                    else:
                        signs[f]=1 if value>=0 else -1;changed=True;stats["forced_signs"]+=1
                    continue
                scale=next(c for c in reduced if c)
                key=tuple(c/scale for c in reduced);sgn=1 if scale>0 else -1
                groups.setdefault(key,[]).append((f,sgn));which[f]=key
            for key,items in groups.items():
                assigned=next(((f,sgn) for f,sgn in items if f in signs),None)
                if assigned is None:continue
                f0,sgn0=assigned;orientation=signs[f0]*sgn0
                for f,sgn in items:
                    if f not in signs:
                        signs[f]=orientation*sgn;changed=True;stats["forced_signs"]+=1
            if not changed:break
        if not exact_lp.feasible(E,I,n):return False
        if not pending:return True
        expr,rhs=min(pending,key=lambda er:(len({which[f] for f in er[0] if f not in signs}),len(er[0])))
        keys={which[f] for f in expr if f not in signs}
        key=max(sorted(keys),key=lambda key:sum(any(which.get(f)==key for f in e if f not in signs) for e,r in pending))
        items=groups[key]
        assert all(f not in signs for f,sgn in items)
        first,sgnfirst=items[0]
        for orientation in (1,-1):
            ss=dict(signs)
            for f,sgn in items:ss[f]=orientation*sgn
            stats["group_branches"]+=1
            if rec(ss,pending,E,I+[[Q(0)]+[orientation*sgnfirst*x for x in first]]):return True
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
        found,stats=affine_dfs(ray_problem(zs,ds));result={"status":"SURVIVOR" if found else "AFFINE_EXCLUDED","stats":stats}
    except TimeoutError:result={"status":"TIMEOUT"}
    result.update({"flats":zs,"signs":ds,"seconds":time.monotonic()-t,"lp":exact_lp.STATS,
                   "trust":"exact affine simplification and rational Farkas pruning; no independent checker yet"})
    with open("overnight_fixed_bowtie_k3_affine.jsonl","a") as out:out.write(json.dumps(result,separators=(",",":"))+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
