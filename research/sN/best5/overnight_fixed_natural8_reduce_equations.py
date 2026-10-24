"""Probe whether one negative-corner ray identity suffices with localities.

Rechecks only cases whose existing proof uses another ray equation.
Exclusions require new rational Farkas witnesses; survivors only show
that this particular cone relaxation cannot give the proposed shortcut.
"""
import gzip
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_natural8_certify import equations
from overnight_fixed_k2_certify import certified_feasible


def main():
    start=time.monotonic();allowed=set(range(26))|{36};total=already=excluded=0;survivors=[]
    with gzip.open("overnight_fixed_natural8_proof.jsonl.gz","rt") as inp,Path("overnight_fixed_natural8_reduced_cases.jsonl").open("w") as out:
        for line in inp:
            r=json.loads(line);total+=1
            if all(i in allowed for i,c in r["proof"][1]):already+=1;continue
            m,rows=equations(r["flats"],r["signs"])
            E=[(["e",i],[-rhs]+[e.get(j,Q(0)) for j in range(m)]) for i,(e,rhs) in enumerate(rows) if i in allowed]
            I=[(["y",i],[Q(0)]+[Q(int(i==j)) for j in range(m)]) for i in range(m)]
            feasible,proof=certified_feasible(E,I,m)
            record={"flats":r["flats"],"signs":r["signs"],"status":"SURVIVOR" if feasible else "EXACT_EXCLUSION"}
            if feasible:survivors.append(record)
            else:
                excluded+=1;ee=[];yy=[]
                for (typ,i),c in proof:(ee if typ=="e" else yy).append([i,c])
                record["proof"]=["cone",ee,yy,[]]
            out.write(json.dumps(record,separators=(",",":"))+"\n")
    result={"status":"27_EQUATIONS_SUFFICE" if not survivors else "27_EQUATION_SHORTCUT_INCOMPLETE","total":total,
        "old_proofs_already_use_only_27":already,"new_exact_exclusions":excluded,"survivors":len(survivors),
        "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_natural8_reduce_equations.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
