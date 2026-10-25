"""Exact global network verification with comparison features and full anchors.

Supports any number of coordinate anchor pairs. Reads the actual physical
network, reconstructs input gradients on every braid cone, cancels every
interior hinge, and checks the remaining maximizing-coordinate gradient.
No producer, SMT model, feature-ray fitter, or numerical library is imported.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json,hashlib,time,sys


def check(path):
    start=time.monotonic();net=json.loads(Path(path).read_text());N=net['N'];A=[list(map(Q,row))for row in net['first_layer']];W=[list(map(Q,row))for row in net['second_layer']];D=list(map(Q,net['output']));assert len(D)==len(W)and D[:2]==[1,-1]and W[1]==[-x for x in W[0]];assert all(len(row)==N for row in A)and all(len(row)==len(A)for row in W);comparisons=[];carriers={}
    for j,row in enumerate(A):
        nz=[i for i,x in enumerate(row)if x]
        if len(nz)==1:
            i=nz[0];assert row[i]in(1,-1)and(i,int(row[i]))not in carriers;carriers[i,int(row[i])]=j
        else:
            assert len(nz)==2 and sum(row)==0;positive=next(i for i,x in enumerate(row)if x>0);negative=next(i for i,x in enumerate(row)if x<0);comparisons.append((j,positive,negative))
    anchors=sorted({i for i,s in carriers});assert anchors and set(carriers)=={(i,s)for i in anchors for s in(1,-1)};anchor_grad=[]
    for k,w in enumerate(W):
        g=[Q(0)]*N
        for i in anchors:assert w[carriers[i,-1]]==-w[carriers[i,1]];g[i]=w[carriers[i,1]]
        assert sum(g)==(1 if k==0 else-1 if k==1 else 0);anchor_grad.append(g)
    cones=groups=0
    for p in permutations(range(N)):
        rank={v:i for i,v in enumerate(p)};act={j:(A[j]if rank[i]<rank[k]else[Q(0)]*N)for j,i,k in comparisons};linear=[anchor_grad[0][i]+sum(W[0][j]*row[i]for j,row in act.items())for i in range(N)];curvature={}
        for k in range(2,len(W)):
            d=D[k];g=tuple(anchor_grad[k][i]+sum(W[k][j]*row[i]for j,row in act.items())for i in range(N));assert sum(g)==0;partial=[sum(g[p[j]]for j in range(t))for t in range(1,N)]
            if min(partial)>=0:linear=[x+d*y for x,y in zip(linear,g)];continue
            if max(partial)<=0:continue
            sc=next(x for x in g if x);normal=tuple(x/sc for x in g);curvature[normal]=curvature.get(normal,Q(0))+d*abs(sc)
            if sc<0:linear=[x+d*y for x,y in zip(linear,g)]
        assert all(v==0 for v in curvature.values()),('UNCANCELLED_INTERIOR_WALL',p,curvature)
        assert linear==[Q(i==p[0])for i in range(N)],('WRONG_LINEAR_GRADIENT',p,linear)
        cones+=1;groups+=len(curvature)
    return{'status':'INDEPENDENT_EXACT_GLOBAL_ANCHOR_NETWORK_PASS','N':N,'h1':len(A),'h2':len(W),'coordinate_anchors':anchors,'comparison_rows':len(comparisons),'braid_cones':cones,'interior_wall_groups':groups,'seconds':time.monotonic()-start,'network_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=='__main__':
    result=check(sys.argv[1]);output=Path(sys.argv[2])if len(sys.argv)>2 else Path(sys.argv[1]).with_suffix('.anchorcheck.json');output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True))
