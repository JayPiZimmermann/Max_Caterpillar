"""Global exact verification for comparison features and coordinate ReLUs.

There is no prescribed second-layer head or anchor-pair cancellation. The
extra ordered label is a fixed zero coordinate. Its braid fan has (N+1)!
full cones whose ray inequalities decide the sign of every linear form.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib,json,time,sys


def check(path):
    start=time.monotonic();path=Path(path);net=json.loads(path.read_text());N=net['N'];A=[list(map(Q,r))for r in net['first_layer']];W=[list(map(Q,r))for r in net['second_layer']];D=list(map(Q,net['output']));assert len(W)==len(D);assert all(len(r)==N for r in A)and all(len(r)==len(A)for r in W);edges=[]
    for row in A:
        nz=[i for i,x in enumerate(row)if x]
        if len(nz)==1:
            i=nz[0];edges.append((i,N)if row[i]>0 else(N,i))
        else:
            assert len(nz)==2 and sum(row)==0;edges.append((next(i for i,x in enumerate(row)if x>0),next(i for i,x in enumerate(row)if x<0)))
    cones=groups=0
    for p in permutations(range(N+1)):
        rank={v:i for i,v in enumerate(p)};rays=[[Q(i in p[:t])-Q(N in p[:t])for i in range(N)]for t in range(1,N+1)];act=[row if rank[i]<rank[j]else[Q(0)]*N for row,(i,j)in zip(A,edges)];linear=[Q(0)]*N;curvature={}
        for w,d in zip(W,D):
            g=tuple(sum(w[j]*act[j][i]for j in range(len(A)))for i in range(N));evaluations=[sum(x*y for x,y in zip(g,r))for r in rays]
            if min(evaluations)>=0:linear=[x+d*y for x,y in zip(linear,g)];continue
            if max(evaluations)<=0:continue
            scale=next(x for x in g if x);normal=tuple(x/scale for x in g);curvature[normal]=curvature.get(normal,Q(0))+d*abs(scale)
            if scale<0:linear=[x+d*y for x,y in zip(linear,g)]
        assert all(v==0 for v in curvature.values()),('UNCANCELLED_INTERIOR_WALL',p,curvature)
        top=next(i for i in p if i<N);assert linear==[Q(i==top)for i in range(N)],('WRONG_LINEAR_GRADIENT',p,linear)
        cones+=1;groups+=len(curvature)
    return{'status':'INDEPENDENT_EXACT_FULL_PHYSICAL_NETWORK_PASS','N':N,'h1':len(A),'h2':len(W),'augmented_braid_cones':cones,'interior_wall_groups':groups,'seconds':time.monotonic()-start,'network_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__=='__main__':
    receipt=check(sys.argv[1]);out=Path(sys.argv[2])if len(sys.argv)>2 else Path(sys.argv[1]).with_suffix('.physicalcheck.json');out.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print(json.dumps(receipt,sort_keys=True))
