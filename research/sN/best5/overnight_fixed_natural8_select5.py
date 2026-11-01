"""Bounded heuristic selector of five flat/sign patterns.

The mixed-integer model convexifies each absolute-value image and caps
the auxiliary magnitudes. Only a proposed pattern can be used; neither
infeasibility nor a feasible relaxation proves a network statement.
"""
import argparse
import hashlib
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import coo_matrix
from overnight_fixed_natural8_k4 import FLATS,SETS,REL,TARGET,data
from overnight_fixed_circuits import block_circuits


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--bound",type=float,default=10);ap.add_argument("--budget",type=int,default=300)
    ap.add_argument("--circuits",action="store_true");ap.add_argument("--attempt",type=int,default=0)
    args=ap.parse_args();start=time.monotonic();patterns=[];columns=[];groupof=[];cuts=[]
    locality=[(U,o) for U in REL if len(U)==3 for o in range(5) if o not in U]
    locality += [(U,None) for U in SETS if len(U) in (4,5)]
    for z in sorted(FLATS):
        _,cubes,rays=data(z);rows=[]
        for U,o in locality:
            active=len(U)==5 or z>>REL.index(U)&1
            if o is not None:active=active and z>>REL.index(U|{o})&1
            rows.append(cubes.get(U,{}) if active else {})
        rows+=rays;forms=sorted({f for e in rows for f in e})
        for d in (1,-1):
            group=len(patterns);patterns.append((z,d));offset=len(columns)
            for f in forms:
                columns.append([float(d*e.get(f,Q(0))) for e in rows]);groupof.append(group)
            if args.circuits:
                for rel in block_circuits(tuple(forms),4):
                    for focus,_ in rel:cuts.append({offset+i:float(abs(c)*(-1 if i==focus else 1)) for i,c in rel})
    m=len(columns);g=len(patterns);n=m+g;ri=[];ci=[];values=[]
    for j,col in enumerate(columns):
        for i,c in enumerate(col):
            if c:ri.append(i);ci.append(j);values.append(c)
    rhs=[float(2*(-1)**(len(U)+1)) for U,o in locality]+list(map(float,TARGET))
    lo=list(rhs);hi=list(rhs)
    for cut in cuts:
        row=len(lo)
        for j,c in cut.items():ri.append(row);ci.append(j);values.append(c)
        lo.append(0);hi.append(np.inf)
    for j,k in enumerate(groupof):
        row=len(lo);ri.extend((row,row));ci.extend((j,m+k));values.extend((1,-args.bound));lo.append(-np.inf);hi.append(0)
    row=len(lo)
    for k in range(g):ri.append(row);ci.append(m+k);values.append(1)
    lo.append(-np.inf);hi.append(5)
    for q in range(25):
        row=len(lo)
        for k,(z,d) in enumerate(patterns):
            if FLATS[z]["cover"]>>q&1:ri.append(row);ci.append(m+k);values.append(1)
        lo.append(1);hi.append(np.inf)
    excluded=set();pattern_index={p:i for i,p in enumerate(patterns)}
    for path in Path('.').glob('overnight_fixed_natural8_select5_*.json'):
        old=json.loads(path.read_text());chosen=old.get('chosen',[])
        if len(chosen)!=5:continue
        key=tuple(sorted(tuple(p) for p in chosen))
        if key in excluded:continue
        excluded.add(key);row=len(lo)
        for p in key:ri.append(row);ci.append(m+pattern_index[p]);values.append(1)
        lo.append(-np.inf);hi.append(4)
    A=coo_matrix((values,(ri,ci)),shape=(len(lo),n)).tocsc()
    c=np.r_[np.zeros(m),np.ones(g)];integrality=np.r_[np.zeros(m,dtype=int),np.ones(g,dtype=int)]
    result=milp(c=c,integrality=integrality,bounds=Bounds(np.zeros(n),np.r_[np.full(m,args.bound),np.ones(g)]),
        constraints=LinearConstraint(A,np.asarray(lo),np.asarray(hi)),
        options={"time_limit":args.budget,"threads":1,"mip_rel_gap":0})
    record={"status":"HEURISTIC_PATTERN_CANDIDATE" if result.x is not None else "NO_HEURISTIC_CANDIDATE",
        "solver_status":int(result.status),"message":result.message,"bound":args.bound,"budget":args.budget,
        "columns":m,"patterns":g,"circuit_rows":len(cuts),"excluded_previous_patterns":len(excluded),"seconds":time.monotonic()-start,
        "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Bounded convexified mixed-integer pattern selector only"}
    if result.x is not None:
        chosen=[patterns[k] for k in range(g) if result.x[m+k]>.5];record["chosen"]=chosen
        record["objective"]=float(result.fun);record["mip_gap"]=float(result.mip_gap)
    name="overnight_fixed_natural8_select5_"+str(int(args.bound))+("_circuits" if args.circuits else "")+"_"+str(args.attempt)+".json"
    Path(name).write_text(json.dumps(record,sort_keys=True,indent=2)+"\n");print(json.dumps(record,sort_keys=True),flush=True)


if __name__=="__main__":main()
