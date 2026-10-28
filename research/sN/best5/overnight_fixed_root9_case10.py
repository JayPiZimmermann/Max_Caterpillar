"""Unbounded closed-sign proof search for one sampled K4 case.
No coefficient box or strict sign margin occurs in this proof search.
"""
import hashlib
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import overnight_root9_equations as engine
from overnight_fixed_k2_certify import certified_feasible


def main():
    start=time.monotonic();engine.initialize();zs=(23655,30836,31220,32316);ds=(1,-1,1,1)
    equation,forms,off=engine.case_data(zs,ds);n=off[-1];rows=[equation(i)for i in range(49)];initial={};I=[];nodes=0
    for k in range(4):
        j=next(j for j,f in enumerate(forms)if any(f[off[k]:off[k+1]]));initial[j]=1;I.append((["f",j],[Q(0)]+list(forms[j])))
    def dfs(sg,pending,E,I):
        nonlocal nodes
        nodes+=1;left=[];EE=list(E)
        for i in pending:
            e,rhs=rows[i]
            if all(j in sg for j in e):
                row=[-rhs]+[sum(c*sg[j]*forms[j][p]for j,c in e.items())for p in range(n)]
                if not any(row[1:]):
                    if row[0]:return["constant",i]
                    continue
                EE.append((["e",i],row))
            else:left.append(i)
        feasible,proof=certified_feasible(EE,I,n)
        if not feasible:return["farkas",proof]
        if not left:raise ValueError("NECESSARY_CONDITION_SURVIVOR")
        ei=min(left,key=lambda i:(sum(j not in sg for j in rows[i][0]),len(rows[i][0])))
        j=max((j for j in rows[ei][0]if j not in sg),key=lambda j:sum(j in rows[i][0]for i in left))
        children=[]
        for s in(1,-1):
            ss=dict(sg);ss[j]=s;children.append(dfs(ss,left,EE,I+[(["f",j],[Q(0)]+[s*c for c in forms[j]])]))
        return["split",j,*children]
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")));signal.alarm(60)
    result={"flats":zs,"signs":ds}
    try:result.update(status="EXACT_TREE_PRODUCED",proof=dfs(initial,list(range(49)),[],I))
    except(TimeoutError,ValueError)as exc:result.update(status=str(exc))
    finally:signal.alarm(0)
    result.update(nodes=nodes,seconds=time.monotonic()-start,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path("overnight_fixed_root9_case10.json").write_text(json.dumps(result,separators=(",",":"))+"\n")
    print(json.dumps({k:v for k,v in result.items()if k!="proof"},sort_keys=True),flush=True)


if __name__=="__main__":main()
