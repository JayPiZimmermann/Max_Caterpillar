"""Exact exclusion search with canonical absolute-value forms.

Contract: necessary 3-, 4-, 5-tie equations for two translation-invariant
pair-feature neurons, on the whole closed vanishing flats. Positive LP
answers are only conservative; every negative answer uses exact_lp's
rational Farkas verification. This is a search checker, not a Lean proof.
All real and boundary points are covered by the two closed sign branches.
"""
import argparse
import hashlib
import itertools
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path

import exact_lp
from k2_exact import F, REL, IDX, cov
from k2b import reduce_constraints
from k2c import allforms, ALLSETS, FOUR, FULL


def canonical(row):
    first = next((x for x in row if x), None)
    if first is None:
        return None, Q(0)
    return tuple(x / first for x in row), abs(first)


def equations(Zs, d, use5=True):
    good, cons = reduce_constraints([set(cov(Z)) for Z in Zs], d)
    if not good:
        return None
    for U in FOUR:
        ks = [k for k in range(len(Zs)) if Zs[k] >> IDX[U] & 1]
        if not ks:
            return None
        cons.append((U, {k: Q(d[k]) for k in ks}, Q(-1)))
    if use5:
        cons.append((FULL, {k: Q(d[k]) for k in range(len(Zs))}, Q(1)))
    data = [allforms(Z) for Z in Zs]
    offsets = [0]
    for fm, dim in data:
        offsets.append(offsets[-1] + dim)
    n = offsets[-1]
    rows = []
    for U, coef, rhs in cons:
        expr = {}
        for k, c in coef.items():
            for W in ALLSETS:
                if not W < U:
                    continue
                lifted = [Q(0)] * n
                lifted[offsets[k]:offsets[k+1]] = data[k][0][W]
                form, scale = canonical(lifted)
                if form is not None:
                    expr[form] = expr.get(form, Q(0)) + c * scale * (-1)**(len(U)-len(W))
        rows.append(({f:c for f,c in expr.items() if c}, 2*rhs))
    return n, offsets, rows


def check(Zs, d, use5=True):
    problem = equations(Zs, d, use5)
    stats = {"nodes": 0, "branches": 0, "equations": 0}
    if problem is None:
        return False, stats
    n, offsets, initial = problem
    forms = sorted({f for e,r in initial for f in e})
    # All equations contain absolute values. Reversing a whole neuron is
    # harmless modulo the free remainder, so fix one form per neuron >=0.
    initial_signs = {}
    initial_ineqs = []
    for k in range(len(Zs)):
        f = next((f for f in forms if any(f[offsets[k]:offsets[k+1]])), None)
        if f is not None:
            initial_signs[f] = 1
            initial_ineqs.append([Q(0)] + list(f))

    def recur(signs, pending, E, I):
        stats["nodes"] += 1
        E2 = list(E)
        left = []
        for expr, rhs in pending:
            if all(f in signs for f in expr):
                row = [-rhs] + [sum(c*signs[f]*f[j] for f,c in expr.items()) for j in range(n)]
                if not any(row[1:]):
                    if row[0]:
                        return False
                    continue
                E2.append(row)
                stats["equations"] += 1
            else:
                left.append((expr,rhs))
        if not exact_lp.feasible(E2,I,n):
            return False
        if not left:
            return True
        # A completed equation provides an affine restriction immediately.
        expr,rhs = min(left,key=lambda er: (sum(f not in signs for f in er[0]),len(er[0])))
        unknown = [f for f in expr if f not in signs]
        f = max(unknown,key=lambda f: sum(f in e for e,r in left))
        for s in (1,-1):
            stats["branches"] += 1
            ss = dict(signs)
            ss[f] = s
            if recur(ss,left,E2,I+[[Q(0)]+[s*x for x in f]]):
                return True
        return False

    result = recur(initial_signs,initial,[],initial_ineqs)
    stats["canonical_forms"] = len(forms)
    stats["variables"] = n
    return result,stats


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("indices",nargs="*",type=int)
    ap.add_argument("--budget",type=int,default=1200)
    ap.add_argument("--output",default="overnight_fixed_k2_receipts.jsonl")
    ap.add_argument("--all-signs",action="store_true")
    ap.add_argument("--all-pairs",action="store_true")
    ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--stop",type=int,default=1000000)
    args=ap.parse_args()
    # One bounded process; append only completed per-sign receipts.
    def timeout(*_):
        raise TimeoutError("declared wall-clock budget reached")
    signal.signal(signal.SIGALRM,timeout)
    signal.alarm(args.budget)
    import ast
    cases=[]
    if args.all_pairs:
        import pickle
        work=pickle.load(open("k2_work.pkl","rb"))
        for idx,zs in enumerate(work):
            if args.start<=idx<args.stop:
                cases.append((idx,list(zs),list(itertools.product((1,-1),repeat=2))))
    else:
        for line in open("k2b_survivors.txt"):
            idx,status,z1,z2,signs=line.split(maxsplit=4)
            if args.indices and int(idx) not in args.indices:
                continue
            ds=list(itertools.product((1,-1),repeat=2)) if args.all_signs else ast.literal_eval(signs)
            cases.append((int(idx),[int(z1),int(z2)],ds))
    producer=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    done=set()
    if Path(args.output).exists():
        for line in Path(args.output).read_text().splitlines():
            old=json.loads(line)
            if old.get("producer_sha256")==producer:
                done.add((old["case"],tuple(old["signs"])))
    started=time.monotonic()
    try:
        for idx,Zs,ds in cases:
            for d in ds:
                if (idx,tuple(d)) in done:
                    continue
                before=list(exact_lp.STATS)
                t=time.monotonic()
                found,stats=check(Zs,d)
                row={"case":idx,"flats":Zs,"signs":d,"status":"SURVIVOR" if found else "EXCLUDED",
                     "stats":stats,"lp_counts":[a-b for a,b in zip(exact_lp.STATS,before)],
                     "seconds":time.monotonic()-t,"producer_sha256":producer}
                with open(args.output,"a") as out:
                    out.write(json.dumps(row,sort_keys=True)+"\n")
                print(json.dumps(row,sort_keys=True),flush=True)
    except TimeoutError:
        print(json.dumps({"status":"BUDGET_EXHAUSTED","seconds":time.monotonic()-started}),flush=True)
        raise SystemExit(124)
    print(json.dumps({"status":"COMPLETE","seconds":time.monotonic()-started}),flush=True)


if __name__=="__main__":
    main()
