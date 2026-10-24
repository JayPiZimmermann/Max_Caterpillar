"""Produce a durable rational Farkas proof tree for all K=2 cases.

The verifier independently regenerates direct locality equations and checks
every leaf without an LP solver. Branches are closed signs, with one
global sign symmetry fixed independently per neuron.
"""
import gzip
import hashlib
import itertools
import json
import pickle
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np

import exact_lp
import fastlp
from overnight_fixed_k2 import equations

COUNTS={"lp":0,"farkas":0,"constant":0,"split":0,"case":0}


def certified_feasible(E,I,n):
    COUNTS["lp"]+=1
    rows=[r for label,r in E+I]
    labels=[label for label,r in E+I]
    if not rows:return True,None
    a=np.asarray([[float(c) for c in row[1:]] for row in rows])
    c0=np.asarray([float(row[0]) for row in rows])
    lo=-c0.copy();hi=np.full(len(rows),np.inf);hi[:len(E)]=-c0[:len(E)]
    name,x,_=fastlp.solve(np.zeros(n),a,lo,hi,np.full(n,-np.inf),np.full(n,np.inf))
    if name=="Optimal":return True,None
    # Any proposed contradiction must have a rational Farkas witness;
    # an ambiguous solver response is conservatively feasible.
    m=len(rows);b=np.zeros((n+1,m));b[:n]=a.T;b[n]=-c0
    lb=np.full(m,-np.inf);lb[len(E):]=0
    target=np.r_[np.zeros(n),1.]
    name,u,_=fastlp.solve(np.zeros(m),b,target,target,lb,np.full(m,np.inf))
    if name!="Optimal":return True,None
    supp=[i for i in range(m) if abs(u[i])>1e-10]
    eq=[[Q(0)]+[-rows[i][j+1] for i in supp] for j in range(n)]
    eq.append([Q(1)]+[rows[i][0] for i in supp])
    sol=exact_lp.solve_eq(eq,len(supp))
    if sol is None:return True,None
    if any(sol[k]<0 for k,i in enumerate(supp) if i>=len(E)):return True,None
    assert all(sum(sol[k]*rows[i][j+1] for k,i in enumerate(supp))==0 for j in range(n))
    assert sum(sol[k]*rows[i][0] for k,i in enumerate(supp))<0
    COUNTS["farkas"]+=1
    return False,[[labels[i],str(sol[k])] for k,i in enumerate(supp) if sol[k]]


def certify(Zs,d):
    problem=equations(Zs,d)
    if problem is None:return ["formal_inconsistent"]
    n,offsets,rows=problem
    forms=sorted({f for e,r in rows for f in e})
    index={f:i for i,f in enumerate(forms)}
    exprs=[({index[f]:c for f,c in e.items()},r) for e,r in rows]
    signs={};I=[]
    for k in range(len(Zs)):
        j=next((j for j,f in enumerate(forms) if any(f[offsets[k]:offsets[k+1]])),None)
        if j is not None:
            signs[j]=1;I.append((["f",j],[Q(0)]+list(forms[j])))

    def dfs(signs,pending,E,I):
        left=[];EE=list(E)
        for ei in pending:
            expr,rhs=exprs[ei]
            if all(j in signs for j in expr):
                row=[-rhs]+[sum(c*signs[j]*forms[j][p] for j,c in expr.items()) for p in range(n)]
                if not any(row[1:]):
                    if row[0]:
                        COUNTS["constant"]+=1
                        return ["constant",ei]
                    continue
                EE.append((["e",ei],row))
            else:left.append(ei)
        feasible,certificate=certified_feasible(EE,I,n)
        if not feasible:return ["farkas",certificate]
        if not left:raise RuntimeError("necessary-equation survivor; no exclusion certificate")
        ei=min(left,key=lambda ei:(sum(j not in signs for j in exprs[ei][0]),len(exprs[ei][0])))
        unknown=[j for j in exprs[ei][0] if j not in signs]
        j=max(unknown,key=lambda j:sum(j in exprs[ei][0] for ei in left))
        children=[]
        for s in (1,-1):
            ss=dict(signs);ss[j]=s
            children.append(dfs(ss,left,EE,I+[(["f",j],[Q(0)]+[s*x for x in forms[j]])]))
        COUNTS["split"]+=1
        return ["split",j,*children]
    return dfs(signs,list(range(len(exprs))),[],I)


def main():
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("1200s budget")))
    signal.alarm(1200)
    started=time.monotonic()
    work=pickle.loads(Path("k2_work.pkl").read_bytes())
    path=Path("overnight_fixed_k2_proof.jsonl.gz")
    with gzip.open(path,"wt") as out:
        for idx,zs in enumerate(work):
            for ds in itertools.product((1,-1),repeat=2):
                proof=certify(list(zs),ds)
                out.write(json.dumps({"case":idx,"flats":zs,"signs":ds,"proof":proof},separators=(",",":"))+"\n")
                COUNTS["case"]+=1
            if idx%100==0:print(json.dumps({"last_case":idx,"counts":COUNTS,"seconds":time.monotonic()-started}),flush=True)
    receipt={"status":"PROOF_TREES_COMPLETE","counts":COUNTS,"seconds":time.monotonic()-started,
             "proof_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
             "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "equations_sha256":hashlib.sha256(Path("overnight_fixed_k2.py").read_bytes()).hexdigest()}
    Path("overnight_fixed_k2_producer.json").write_text(json.dumps(receipt,sort_keys=True,indent=2)+"\n")
    print(json.dumps(receipt,sort_keys=True),flush=True)


if __name__=="__main__":main()
