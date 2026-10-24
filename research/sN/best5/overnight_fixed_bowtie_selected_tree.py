"""Closed-sign proof search with only selected pair-ray equations.
Old exact proof files remain read-only. Every leaf carries rational data.
Time limits and necessary-condition survivors are recorded as incomplete.
"""
import argparse
import gzip
import hashlib
import json
import signal
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_bowtie_ray import ray_problem
from overnight_fixed_k2_certify import certified_feasible


def prove(zs,ds,keep):
    p=ray_problem(zs,ds);assert p is not None
    n,offsets,allrows=p;split=len(allrows)-22
    rows=allrows[:split]+[row for i,row in enumerate(allrows[split:],26) if i in keep]
    forms=sorted({f for e,r in rows for f in e});index={f:i for i,f in enumerate(forms)}
    exprs=[({index[f]:c for f,c in e.items()},r) for e,r in rows];signs={};inequalities=[]
    for k in range(3):
        j=next((j for j,f in enumerate(forms) if any(f[offsets[k]:offsets[k+1]])),None)
        if j is not None:signs[j]=1;inequalities.append((["f",j],[Q(0)]+list(forms[j])))
    nodes=0
    def dfs(sg,pending,E,I):
        nonlocal nodes
        nodes+=1;left=[];EE=list(E)
        for ei in pending:
            e,rhs=exprs[ei]
            if all(j in sg for j in e):
                row=[-rhs]+[sum(c*sg[j]*forms[j][p] for j,c in e.items()) for p in range(n)]
                if not any(row[1:]):
                    if row[0]:return ["constant",ei]
                    continue
                EE.append((["e",ei],row))
            else:left.append(ei)
        feasible,cert=certified_feasible(EE,I,n)
        if not feasible:return ["farkas",cert]
        if not left:raise ValueError("NECESSARY_CONDITION_SURVIVOR")
        ei=min(left,key=lambda i:(sum(j not in sg for j in exprs[i][0]),len(exprs[i][0])))
        j=max((j for j in exprs[ei][0] if j not in sg),key=lambda j:sum(j in exprs[i][0] for i in left))
        children=[]
        for s in (1,-1):
            ss=dict(sg);ss[j]=s
            children.append(dfs(ss,left,EE,I+[(["f",j],[Q(0)]+[s*x for x in forms[j]])]))
        return ["split",j,*children]
    proof=dfs(signs,list(range(len(exprs))),[],inequalities)
    return ["tree",{"n":n,"offsets":offsets,"forms":[list(map(str,f)) for f in forms],
                    "rows":[[[[i,str(c)] for i,c in sorted(e.items())],str(rhs)] for e,rhs in exprs]},proof],nodes


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=600);ap.add_argument("--case-budget",type=int,default=15)
    args=ap.parse_args();start=time.monotonic();keep=set(range(26,33));counts=Counter()
    prefix="overnight_fixed_bowtie_selected_pairs_tree";outpath=Path(prefix+".jsonl.gz");done=set()
    if outpath.exists():
        for line in gzip.open(outpath,"rt"):
            r=json.loads(line)
            if r["status"]!="TIMEOUT":done.add((tuple(r["flats"]),tuple(r["signs"])))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("case budget")))
    with Path("overnight_fixed_bowtie_selected_pairs.jsonl").open() as inp,gzip.open(outpath,"at") as out:
        for line in inp:
            old=json.loads(line);key=tuple(old["flats"]),tuple(old["signs"])
            if old["status"]!="CONE_SURVIVOR" or key in done:continue
            remaining=args.budget-(time.monotonic()-start)
            if remaining<1:break
            t=time.monotonic();signal.alarm(min(args.case_budget,int(remaining)))
            r={"flats":key[0],"signs":key[1]}
            try:
                proof,nodes=prove(*key,keep);r.update(status="EXACT_TREE_EXCLUSION",proof=proof,nodes=nodes)
            except TimeoutError:r["status"]="TIMEOUT"
            except ValueError as exc:r["status"]=str(exc)
            finally:signal.alarm(0)
            r["seconds"]=time.monotonic()-t;counts[r["status"]]+=1
            out.write(json.dumps(r,separators=(",",":"))+"\n");out.flush()
            print(json.dumps({"processed":sum(counts.values()),"counts":counts,"latest":{k:v for k,v in r.items() if k!="proof"},"seconds":time.monotonic()-start}),flush=True)
    result={"status":"SELECTED_PAIR_TREE_BATCH_COMPLETE","counts":counts,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(prefix+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
