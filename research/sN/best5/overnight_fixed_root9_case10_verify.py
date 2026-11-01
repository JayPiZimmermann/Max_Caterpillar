"""Independent exact verification of one complete sampled K4 sign tree."""
import hashlib
import json
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import overnight_root9_equations as engine


def main():
    start=time.monotonic();r=json.loads(Path("overnight_fixed_root9_case10.json").read_text());assert r["status"]=="EXACT_TREE_PRODUCED"
    assert r["flats"]==[23655,30836,31220,32316]and r["signs"]==[1,-1,1,1]
    engine.initialize();equation,forms,off=engine.case_data(tuple(r["flats"]),tuple(r["signs"]));n=off[-1];initial={};counts=Counter()
    for k in range(4):initial[next(j for j,f in enumerate(forms)if any(f[off[k]:off[k+1]]))]=1
    def equality(i,sg):
        e,rhs=equation(i);assert all(j in sg for j in e)
        return[-rhs]+[sum(c*sg[j]*forms[j][p]for j,c in e.items())for p in range(n)]
    def visit(node,sg):
        kind=node[0]
        if kind=="split":
            assert len(node)==4;j=node[1];assert 0<=j<len(forms)and j not in sg
            for s,child in zip((1,-1),node[2:]):ss=dict(sg);ss[j]=s;visit(child,ss)
        elif kind=="constant":
            row=equality(node[1],sg);assert row[0]and not any(row[1:])
        elif kind=="farkas":
            total=[Q(0)]*(n+1)
            for(typ,i),raw in node[1]:
                c=Q(raw)
                if typ=="e":row=equality(i,sg)
                else:
                    assert typ=="f"and i in sg and c>=0;row=[Q(0)]+[sg[i]*v for v in forms[i]]
                total=[a+c*b for a,b in zip(total,row)]
            assert total[0]<0 and not any(total[1:])
        else:raise AssertionError(kind)
        counts[kind]+=1
    visit(r["proof"],initial)
    result={"status":"INDEPENDENT_EXACT_SAMPLED_K4_CASE10_EXCLUSION_PASS","counts":counts,"seconds":time.monotonic()-start,
            "proof_sha256":hashlib.sha256(Path("overnight_fixed_root9_case10.json").read_bytes()).hexdigest(),
            "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"scope":"Only the specified single flat/sign case; all real coefficients and closed signs"}
    Path("overnight_fixed_root9_case10_check.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True))


if __name__=="__main__":main()
