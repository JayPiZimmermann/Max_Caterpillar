"""Independent exact proof for an enlarged-first-layer activation-pattern witness.

Standard library only. The checker does not import the search, cofactor ray
producer, numerical optimizer, or any generated arrangement inventory.
"""
import argparse,hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path


def canonical(row):
    row=list(map(Q,row));den=math.lcm(*(c.denominator for c in row));v=[int(c*den)for c in row];g=math.gcd(*v)
    if not g:return None
    if next(c for c in v if c)<0:g=-g
    return tuple(c//g for c in v)


def kernel_ray(rows):
    matrix=[list(map(Q,row))for row in rows];pivots=[];at=0
    for c in range(4):
        pivot=next((r for r in range(at,len(matrix))if matrix[r][c]),None)
        if pivot is None:continue
        matrix[at],matrix[pivot]=matrix[pivot],matrix[at];p=matrix[at][c];matrix[at]=[x/p for x in matrix[at]]
        for r in range(len(matrix)):
            if r!=at:
                t=matrix[r][c];matrix[r]=[x-t*y for x,y in zip(matrix[r],matrix[at])]
        pivots.append(c);at+=1
    if len(pivots)!=3:return None
    free=next(c for c in range(4)if c not in pivots);v=[Q(0)]*4;v[free]=1
    for row,p in zip(matrix,pivots):v[p]=-row[free]
    return canonical(v)


def check(netpath,witnesspath):
    start=time.monotonic();net=json.loads(Path(netpath).read_text());witness=json.loads(Path(witnesspath).read_text());assert net['N']==5;A=[list(map(Q,row))for row in net['first_layer']];W=[list(map(Q,row))for row in net['second_layer']];d=list(map(Q,net['output']));nf=len(A)-2;K=len(W)-2;assert len(d)==len(W);assert K==len(witness['initial_forms']);assert all(len(row)==5 for row in A);assert all(len(row)==len(A)for row in W);assert A[-2:]==[[1,0,0,0,0],[-1,0,0,0,0]];assert d[:2]==[1,-1];assert W[0][-2:]==[1,-1];assert W[1]==[-c for c in W[0]];assert all(row[-2:]==[0,0]for row in W[2:]);assert all(sum(a)==0 for a in A[:-2]);assert [[Q(c)for c in row]for row in witness['first_layer']]==A[:-2];assert list(map(Q,witness['remainder']))==W[0][:-2];assert [list(map(Q,row))for row in witness['outer_forms']]==[row[:-2]for row in W[2:]];assert list(map(Q,witness['output']))==d[2:]
    H={canonical(a)for a in A[:-2]};assert None not in H
    for i,j in itertools.combinations(range(5),2):
        a=[0]*5;a[i]=1;a[j]=-1;assert canonical(a)in H
    old=[list(map(Q,row))for row in witness['initial_forms']];assert all(len(row)==nf for row in old);pair=[]
    for a in A[:-2]:
        nz=[i for i,c in enumerate(a)if c]
        pair.append(len(nz)==2 and a[nz[0]]==-a[nz[1]])
    assert all(not c or pair[i]for row in old for i,c in enumerate(row))
    # Every old zero inside a braid cone lies on an actual first-layer
    # hyperplane. Thus old signs are constant on each refined cone.
    mixed=0
    for perm in itertools.permutations(range(5)):
        rank={i:k for k,i in enumerate(perm)};active=[]
        for a,is_pair in zip(A[:-2],pair):
            if not is_pair:active.append([Q(0)]*5);continue
            i=next(i for i,c in enumerate(a)if c>0);j=next(i for i,c in enumerate(a)if c<0);active.append(a if rank[i]<rank[j]else[Q(0)]*5)
        for row in old:
            g=[sum(c*a[i]for c,a in zip(row,active))for i in range(5)];values=[sum(g[perm[i]]for i in range(k))for k in range(1,5)]
            if min(values)<0<max(values):assert canonical(g)in H;mixed+=1
    lines=set()
    for normals in itertools.combinations(sorted(H),3):
        ray=kernel_ray([h[1:]for h in normals])
        if ray:lines.add(ray)
    rays=0
    for line in lines:
        for sign in(1,-1):
            x=[Q(0)]+[Q(sign*c)for c in line];phi=[max(sum(a*c for a,c in zip(row,x)),Q(0))for row in A[:-2]];actual=[sum(c*f for c,f in zip(row[:-2],phi))for row in W[2:]]
            for row,value in zip(old,actual):
                previous=sum(c*f for c,f in zip(row,phi))
                assert (previous>0 and value>=0)or(previous<0 and value<=0)or(previous==value==0)
            answer=sum(c*f for c,f in zip(W[0][:-2],phi))+sum(out*max(value,Q(0))for out,value in zip(d[2:],actual));assert answer==max(x);rays+=1
    return{'status':'INDEPENDENT_EXACT_ENLARGED_NETWORK_PASS','N':5,'h1':len(A),'h2':len(W),'first_hyperplanes':len(H),'arrangement_rays':rays,'old_mixed_braid_restrictions':mixed,'network_sha256':hashlib.sha256(Path(netpath).read_bytes()).hexdigest(),'witness_sha256':hashlib.sha256(Path(witnesspath).read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-start}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('network');ap.add_argument('witness');ap.add_argument('--output');args=ap.parse_args();r=check(args.network,args.witness)
    if args.output:Path(args.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps(r,sort_keys=True))

if __name__=='__main__':main()
