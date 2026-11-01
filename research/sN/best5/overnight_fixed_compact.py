"""Probe a branch-free circuit/Farkas proof for the full K=2 theorem."""
import gzip
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import exact_lp
from overnight_fixed_circuits import inequalities


def main():
    t=time.monotonic();counts={"constant":0,"nonnegative":0,"circuit4":0,"survivor":0};survivors=[]
    with gzip.open("overnight_fixed_k2_systems.jsonl.gz","rt") as inp,open("overnight_fixed_compact.jsonl","w") as out:
        for pos,line in enumerate(inp):
            rec=json.loads(line);s=rec["system"]
            if s is None:stage="constant"
            else:
                forms=[tuple(Q(c) for c in f) for f in s["forms"]];m=len(forms)
                rows=[({int(i):Q(c) for i,c in ts},Q(rhs)) for ts,rhs in s["rows"]]
                if any((r>0 and all(c<=0 for c in e.values())) or (r<0 and all(c>=0 for c in e.values())) for e,r in rows):stage="constant"
                else:
                    E=[[-r]+[e.get(i,Q(0)) for i in range(m)] for e,r in rows]
                    I=[[Q(0)]+[Q(int(i==j)) for j in range(m)] for i in range(m)]
                    if not exact_lp.feasible(E,I,m):stage="nonnegative"
                    else:
                        I+=inequalities(forms,s["offsets"],4)
                        if not exact_lp.feasible(E,I,m):stage="circuit4"
                        else:stage="survivor";survivors.append([rec["case"],rec["signs"]])
            counts[stage]+=1
            out.write(json.dumps({"case":rec["case"],"signs":rec["signs"],"stage":stage},separators=(",",":"))+"\n")
            if pos%400==0:print(json.dumps({"processed":pos+1,"counts":counts,"seconds":time.monotonic()-t}),flush=True)
    result={"status":"COMPLETE","counts":counts,"survivors":survivors,"seconds":time.monotonic()-t,"lp":exact_lp.STATS}
    Path("overnight_fixed_compact.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
