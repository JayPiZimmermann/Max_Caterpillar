"""Structured construction search on the natural eight-row first layer.

The image of (sigma(u),sigma(v),sigma(u-v)) is the union of three
two-dimensional cones. Enumerate small integer outer forms whose kink
on every product cone is either absent or exactly the desired equality
of the two group maxima. These are globally valid dictionary functions,
so a rational span identity on the braid rays would be a construction.
Failure concerns only this declared coefficient box/admissible family.
"""
import hashlib
import itertools
import json
import math
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import sympy as sp


def group(w,k):
    a,b,p=w
    return [(a+b,a+p),(a+b,b),(a+p,p)][k]


def admissible(w):
    active=[]
    for i,j in itertools.product(range(3),repeat=2):
        v=group(w[:3],i)+group(w[3:],j)
        if min(v)>=0 or max(v)<=0:continue
        target=(1,int(i!=2),-1,-int(j!=2))
        c=v[0]
        if not c or tuple(c*x for x in target)!=v:return None
        active.append((i,j))
    return active


def main():
    started=time.monotonic();box=2;forms=[];cover=[]
    for w in itertools.product(range(-box,box+1),repeat=6):
        first=next((c for c in w if c),None)
        if first is None or first<0 or math.gcd(*w)!=1:continue
        active=admissible(w)
        if active:forms.append(w);cover.append(active)
    # Five labels are (center,u,v,s,t); translation set center=0.
    rays=[S for k in range(1,5) for S in itertools.combinations(range(5),k)]
    features=[];target=[]
    for S in rays:
        x=[int(i in S) for i in range(5)];u,v,s,t=[x[i]-x[0] for i in range(1,5)]
        features.append([max(u,0),max(v,0),max(u-v,0),max(s,0),max(t,0),max(s-t,0)])
        target.append(1-x[0])
    F=np.asarray(features,dtype=np.int64);W=np.asarray(forms,dtype=np.int64)
    outer=np.maximum(F@W.T,0) if forms else np.zeros((30,0),dtype=np.int64)
    matrix=sp.Matrix(np.c_[F,outer]);aug=matrix.row_join(sp.Matrix(target))
    rank=matrix.rank();arank=aug.rank();result={"status":"CONSTRUCTION_DICTIONARY_SPAN" if rank==arank else "DECLARED_DICTIONARY_INSUFFICIENT",
        "coefficient_box":box,"admissible_nontrivial_forms":len(forms),"rank":rank,"augmented_rank":arank,
        "forms":forms,"active_product_cones":cover,"seconds":time.monotonic()-started}
    if rank==arank:
        sol,params=matrix.gauss_jordan_solve(sp.Matrix(target));solution=[Q(str(v.subs({x:0 for x in params}))) for v in sol]
        result["remainder"]=[str(v) for v in solution[:6]]
        result["neurons"]=[[list(w),str(c)] for w,c in zip(forms,solution[6:]) if c]
    result["producer_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path("overnight_fixed_natural8_admissible.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
