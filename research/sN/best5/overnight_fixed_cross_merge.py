"""Exact global pair identities for reducing a constructed network.

Two outer terms may be replaced by one term plus a first-layer remainder
only if every interior crease and every quotient ray value agree exactly.
The searched new normals are rational linear combinations of the old two.
"""
import argparse
import functools
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_bowtie_verify import rref
from overnight_fixed_cross_sparse import exact_check


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--arity",type=int,choices=[2,3,4],default=2);args=ap.parse_args()
    start=time.monotonic();candidate=json.loads(Path("overnight_fixed_cross_polished_candidate.json").read_text());edges=candidate["first_layer_edges"]
    sets=[frozenset(S)for k in range(1,5)for S in itertools.combinations(range(5),k)];ix={S:i for i,S in enumerate(sets)}
    feature=[tuple(Q(int(i in S and j not in S))for i,j in edges)for S in sets]
    rankrows=rref([[feature[S][j]for S in range(30)]for j in range(7)])
    pivots=[next(i for i,c in enumerate(row)if c)for row in rankrows];ANN=[]
    for free in range(30):
        if free in pivots:continue
        row=[Q(0)]*30;row[free]=1
        for pivot,r in zip(pivots,rankrows):row[pivot]=-r[free]
        ANN.append(row)
    cones=[tuple(ix[frozenset(perm[:k])]for k in range(1,5))for perm in itertools.permutations(range(5))]
    def solve_linear(trace):
        rr=rref([list(feature[i])+[trace[i]]for i in pivots]);assert len(rr)==7
        result=[row[-1]for row in rr]
        assert all(sum(a*b for a,b in zip(f,result))==v for f,v in zip(feature,trace))
        return result
    @functools.lru_cache(None)
    def fingerprint(w):
        values=tuple(sum(a*b for a,b in zip(w,f))for f in feature);trace=tuple(max(v,Q(0))for v in values);fp={}
        for q,ids in enumerate(cones):
            v=tuple(values[i]for i in ids)
            if min(v)<0<max(v):
                first=next(c for c in v if c);normal=tuple(c/first for c in v);fp["c",q,normal]=abs(first)
        for q,row in enumerate(ANN):
            value=sum(a*b for a,b in zip(row,trace))
            if value:fp["r",q]=value
        return fp,trace
    def add(out,part,c):
        for k,a in part.items():
            out[k]=out.get(k,Q(0))+c*a
            if not out[k]:del out[k]
    W=[tuple(map(Q,row))for row in candidate["outer_forms"]];D=list(map(Q,candidate["output"]));R=list(map(Q,candidate["remainder"]));steps=[]
    while True:
        W=[tuple(abs(d)*c for c in w)for w,d in zip(W,D)];D=[Q(1 if d>0 else-1)for d in D]
        found=False
        for selected in itertools.combinations(range(len(W)),args.arity):
            target={};combined_trace=[Q(0)]*30
            for i in selected:
                fp,tr=fingerprint(W[i]);add(target,fp,D[i]);combined_trace=[a+D[i]*b for a,b in zip(combined_trace,tr)]
            ratios=(Q(1),Q(-1))if args.arity==4 else(Q(1),Q(-1),Q(2),Q(-2),Q(1,2),Q(-1,2))
            choices=[None]if not target else[tuple(sum(c*W[i][j]for c,i in zip((Q(1),)+tail,selected))for j in range(7))for tail in itertools.product(ratios,repeat=args.arity-1)]
            for w in choices:
                if w is None:coefficient=Q(0);trace=combined_trace
                else:
                    fn,tn=fingerprint(w)
                    if set(fn)!=set(target):continue
                    key=next(iter(target));coefficient=target[key]/fn[key]
                    if any(target[k]!=coefficient*fn[k]for k in target):continue
                    trace=[a-coefficient*b for a,b in zip(combined_trace,tn)]
                remainder=solve_linear(trace);R=[a+b for a,b in zip(R,remainder)]
                keep=[k for k in range(len(W))if k not in selected];W=[W[k]for k in keep]+([w]if coefficient else[]);D=[D[k]for k in keep]+([coefficient]if coefficient else[])
                steps.append({"new_free_width":len(W),"merged_indices":list(selected)});found=True;break
            if found:break
        if not found:break
    control=exact_check(edges,W,R,D)
    result={"status":"EXACT_GLOBAL_MERGE_PASS","initial_free_width":len(candidate["output"]),"final_free_width":len(W),"steps":steps,"check":control,"seconds":time.monotonic()-start}
    out={"first_layer_edges":edges,"remainder":list(map(str,R)),"outer_forms":[list(map(str,w))for w in W],"output":list(map(str,D))}
    suffix=""if args.arity==2 else str(args.arity)
    Path("overnight_fixed_cross_merge"+suffix+"_candidate.json").write_text(json.dumps(out,indent=2)+"\n")
    Path("overnight_fixed_cross_merge"+suffix+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True))


if __name__=="__main__":main()
