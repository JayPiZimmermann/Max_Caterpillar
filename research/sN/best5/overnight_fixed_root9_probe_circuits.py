"""Exact short-circuit strengthening for twelve sampled K4 cases only."""
import argparse
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import overnight_root9_equations as engine
from overnight_fixed_circuits import block_circuits
from overnight_fixed_k2_certify import certified_feasible


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--size",type=int,default=4);args=ap.parse_args()
    start=time.monotonic();engine.initialize();a=engine.arithmetic
    cases=json.loads(Path("overnight_root9_k4_probe.json").read_text())["survivors"];records=[];checked=0
    for ci,case in enumerate(cases):
        zs=tuple(case["flats"]);ds=tuple(case["signs"]);equation,forms,coff=engine.case_data(zs,ds);m=len(forms)
        E=[]
        for i in range(49):
            e,rhs=equation(i);E.append((["e",i],[-rhs]+[e.get(j,Q(0))for j in range(m)]))
        I=[(["y",i],[Q(0)]+[Q(int(i==j))for j in range(m)])for i in range(m)];cuts=[];offset=0
        for z in zs:
            local=a.flat(z)[0]
            for relation in block_circuits(tuple(local),args.size):
                lifted=tuple((j+offset,c)for j,c in relation)
                for focus,c in lifted:
                    row=[Q(0)]*(m+1)
                    for j,v in lifted:row[j+1]=abs(v)*(-1 if j==focus else 1)
                    cuts.append((lifted,focus));I.append((["c",len(cuts)-1],row))
            offset+=len(local)
        feasible,certificate=certified_feasible(E,I,m)
        record={"case":ci,"flats":zs,"signs":ds,"circuit_inequalities":len(cuts),"status":"RELAXATION_SURVIVOR"if feasible else"EXACT_CASE_EXCLUSION"}
        if not feasible:
            ee=[];yy=[];cc=[]
            for(typ,i),raw in certificate:
                c=Q(raw)
                if typ=="e":ee.append([i,str(c)])
                elif typ=="y":yy.append([i,str(c)])
                else:
                    relation,focus=cuts[i];cc.append([[[j,str(v)]for j,v in relation],focus,str(c)])
            proof=["cone",ee,yy,cc];a.cone(proof,equation,forms);record["proof"]=proof;checked+=1
        records.append(record);print(json.dumps({k:v for k,v in record.items()if k!="proof"}),flush=True)
    result={"status":"SAMPLED_SHORT_CIRCUIT_CHECK_COMPLETE","exact_exclusions":checked,"sampled_cases":len(cases),"records":records,
            "maximum_circuit_size":args.size,"seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope":"Only the twelve reported sampled K4 cases; not the complete K4 domain"}
    suffix=""if args.size==4 else str(args.size)
    Path("overnight_fixed_root9_probe_circuits"+suffix+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items()if k!="records"}),flush=True)


if __name__=="__main__":main()
