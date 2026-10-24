"""Independent exact global checker for comparison-feature networks.

Uses input-space linear forms, not the producer's feature-ray matrix.
The first two outer neurons must encode a globally linear skip through
opposite ReLUs. Every other preactivation uses comparison features only.
On each braid cone, all interior hyperplanes must cancel. The remaining
linear form is compared coefficientwise with the maximizing coordinate.
No numerical solver, sample point, or producer module is imported.
"""
import hashlib
import itertools
import json
import sys
import time
from fractions import Fraction as Q
from pathlib import Path


def check(path):
    start=time.monotonic();net=json.loads(Path(path).read_text());N=net["N"]
    A=[list(map(Q,row)) for row in net["first_layer"]];W=[list(map(Q,row)) for row in net["second_layer"]];D=list(map(Q,net["output"]))
    h1=len(A);h2=len(W)
    assert all(len(row)==N for row in A) and len(D)==h2 and all(len(row)==h1 for row in W)
    assert D[:2]==[1,-1] and W[1]==[-c for c in W[0]]
    carrier=A[-2];assert sum(c!=0 for c in carrier)==1 and sum(carrier)==1
    reference=carrier.index(Q(1));assert A[-1]==[-c for c in carrier]
    assert W[0][-2:]==[1,-1] and all(row[-2:]==[0,0] for row in W[2:])
    comparisons=[]
    for row in A[:-2]:
        positive=[i for i,c in enumerate(row) if c>0];negative=[i for i,c in enumerate(row) if c<0]
        assert len(positive)==len(negative)==1 and sum(row)==0
        comparisons.append((positive[0],negative[0]))
    cones=groups=0
    for perm in itertools.permutations(range(N)):
        rank={label:i for i,label in enumerate(perm)}
        active=[row if rank[i]<rank[j] else [Q(0)]*N for row,(i,j) in zip(A[:-2],comparisons)]
        linear=[Q(i==reference)+sum(w*row[i] for w,row in zip(W[0][:-2],active)) for i in range(N)]
        curvature={}
        for d,weights in zip(D[2:],W[2:]):
            g=tuple(sum(w*row[i] for w,row in zip(weights[:-2],active)) for i in range(N));assert sum(g)==0
            if not any(g):continue
            partial=[sum(g[perm[j]] for j in range(k)) for k in range(1,N)]
            if min(partial)>=0:
                linear=[x+d*y for x,y in zip(linear,g)];continue
            if max(partial)<=0:continue
            scale=next(c for c in g if c);normal=tuple(c/scale for c in g)
            curvature[normal]=curvature.get(normal,Q(0))+d*abs(scale)
            # sigma(-z)=sigma(z)-z. After cancellation of the common
            # sigma(normal.x), negative orientations leave d*g.x.
            if scale<0:linear=[x+d*y for x,y in zip(linear,g)]
        assert all(c==0 for c in curvature.values()),("UNCANCELLED_INTERIOR_HYPERPLANE",perm,curvature)
        assert linear==[Q(i==perm[0]) for i in range(N)],("WRONG_LINEAR_FORM",perm,linear)
        cones+=1;groups+=len(curvature)
    return {"status":"INDEPENDENT_EXACT_GLOBAL_COMPARISON_NETWORK_PASS","N":N,"h1":h1,"h2":h2,
            "braid_cones":cones,"cancelled_interior_hyperplane_groups":groups,"seconds":time.monotonic()-start,
            "network_sha256":hashlib.sha256(Path(path).read_bytes()).hexdigest(),
            "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=="__main__":
    result=check(sys.argv[1]);out=Path(sys.argv[2]) if len(sys.argv)>2 else Path(sys.argv[1]).with_suffix(".check.json")
    out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True),flush=True)
