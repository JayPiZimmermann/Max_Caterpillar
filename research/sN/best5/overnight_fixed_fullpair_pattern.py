"""Seek a matched (16,5) construction by enlarging the three-neuron core space.

The paper's fourteen comparison functions span every linear difference
and every coordinate-difference ReLU. The two extra carrier functions are
sigma(x0),sigma(-x0). No sampled identity is accepted.
"""
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from overnight_fixed_cross_pattern import refine
from overnight_fixed_cross_verify import check


EDGES=[(i,0)for i in range(1,5)]+list(itertools.combinations(range(5),2))


def embed(edges,row):
    out=[Q(0)]*14
    for(i,j),raw in zip(edges,row):
        c=Q(raw)
        if(i,j)in EDGES:out[EDGES.index((i,j))]+=c;continue
        out[EDGES.index((j,i))]+=c
        for k,d in((i,c),(j,-c)):
            if k:out[EDGES.index((k,0))]+=d;out[EDGES.index((0,k))]-=d
    return list(map(str,out))


def network(candidate):
    A=[]
    for i,j in EDGES:
        a=[0]*5;a[i]=1;a[j]=-1;A.append(a)
    A.extend([[1,0,0,0,0],[-1,0,0,0,0]]);R=list(map(Q,candidate["remainder"]))
    W=[list(map(str,R))+["1","-1"],list(map(str,[-c for c in R]))+["-1","1"]]
    W.extend(row+["0","0"]for row in candidate["outer_forms"])
    return{"N":5,"first_layer":A,"second_layer":W,"output":["1","-1"]+candidate["output"]}


def main():
    start=time.monotonic();source=json.loads(Path("overnight_fixed_cross_core_search.json").read_text());cores=[r["key"]for r in source["records"]if len(r["key"])==3]
    allW=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")["forms"]
    oldedges=json.loads(Path("overnight_fixed_cross_dictionary_2_orientation3.json").read_text())["first_layer_edges"]
    # Positive control in the enlarged coefficient domain.
    known=json.loads(Path("netB_10_6.json").read_text());knownedges=[]
    for a in known["first_layer"][:-2]:
        row=list(map(Q,a));knownedges.append((row.index(Q(1)),row.index(Q(-1))))
    control={"first_layer_edges":EDGES,"outer_forms":[embed(knownedges,row[:-2])for row in known["second_layer"][2:]],"output":known["output"][2:]}
    positive=refine(control,list(range(4)));assert"candidate"in positive
    path=Path("overnight_fixed_fullpair_pattern_control_net.json");path.write_text(json.dumps(network(positive["candidate"]),indent=2)+"\n")
    controlreceipt=check(path);Path("overnight_fixed_fullpair_pattern_control_check.json").write_text(json.dumps(controlreceipt,sort_keys=True,indent=2)+"\n")
    records=[];found=False
    for ci,core in enumerate(cores):
        candidate={"first_layer_edges":EDGES,"outer_forms":[embed(oldedges,allW[j])for j,d in core],"output":[d for j,d in core]}
        result=refine(candidate,list(range(3)));record={"core":ci,**{k:v for k,v in result.items()if k!="candidate"}};records.append(record)
        if"candidate"in result:
            net=network(result["candidate"]);path=Path("overnight_fixed_fullpair_net16_5.json");path.write_text(json.dumps(net,indent=2)+"\n")
            receipt=check(path);Path("overnight_fixed_fullpair_net16_5_check.json").write_text(json.dumps(receipt,sort_keys=True,indent=2)+"\n")
            record["global_check"]="EXACT_PASS";found=True
        print(json.dumps(record,sort_keys=True),flush=True)
        if found:break
    report={"status":"EXACT_MATCHED_SIXTEEN_FIVE_CONSTRUCTION"if found else"FULLPAIR_CORE_PATTERN_SEARCH_INCOMPLETE",
            "records":records,"positive_control":controlreceipt,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope":"Only three chosen cancellation patterns; negative results imply no general lower bound"}
    Path("overnight_fixed_fullpair_pattern.json").write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
    print(json.dumps(report,sort_keys=True),flush=True)


if __name__=="__main__":main()
