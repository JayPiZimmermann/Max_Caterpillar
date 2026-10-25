"""Exact inventory of signed permutations plus the normalized Hadamard map.

Matrices are stored as twice their entries. Closure is verified exactly;
no group-order assumption or floating-point matrix comparison is used.
"""
import hashlib,itertools,json,math,time
from collections import deque
from pathlib import Path


def multiply(A,B):
    out=[]
    for i in range(4):
        for j in range(4):
            s=sum(A[4*i+k]*B[4*k+j]for k in range(4));assert s%2==0;out.append(s//2)
    return tuple(out)

def canonical(v):
    d=math.gcd(*v)
    if not d:return None
    if next(c for c in v if c)<0:d=-d
    return tuple(c//d for c in v)

def det3(a):return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])


def main():
    start=time.monotonic();I=tuple(2*int(i==j)for i in range(4)for j in range(4));generators=[]
    for k in range(3):
        p=list(range(4));p[k],p[k+1]=p[k+1],p[k];generators.append(tuple(2*int(p[i]==j)for i in range(4)for j in range(4)))
    generators.append(tuple((-2 if i==j==0 else 2*int(i==j))for i in range(4)for j in range(4)));generators.append((1,1,1,1,1,1,-1,-1,1,-1,1,-1,1,-1,-1,1));seen={I};queue=deque([I])
    while queue:
        A=queue.popleft()
        for B in generators:
            C=multiply(A,B)
            if C not in seen:seen.add(C);queue.append(C)
    assert all(multiply(A,tuple(A[4*j+i]for i in range(4)for j in range(4)))==I for A in seen)
    roots={tuple(s*int(k==i)+t*int(k==j)for k in range(4))for i,j in itertools.combinations(range(4),2)for s,t in itertools.product((1,-1),repeat=2)}
    for A in seen:
        for r in roots:
            v=[sum(A[4*i+j]*r[j]for j in range(4))for i in range(4)];assert all(c%2==0 for c in v);assert tuple(c//2 for c in v)in roots
    functions=sorted({tuple(sorted(tuple(A[4*i:4*i+4])for i in range(4)))for A in seen});frames=sorted({tuple(sorted(canonical(row)for row in Q))for Q in functions});frameof=[frames.index(tuple(sorted(canonical(row)for row in Q)))for Q in functions];walls=set()
    for Q in functions:
        walls.update(canonical(row)for row in Q)
        walls.update(canonical(tuple(a-b for a,b in zip(Q[i],Q[j])))for i,j in itertools.combinations(range(4),2))
    assert None not in walls;lines=set()
    for three in itertools.combinations(sorted(walls),3):
        v=[(-1)**j*det3([[r[k]for k in range(4)if k!=j]for r in three])for j in range(4)];p=canonical(v)
        if p:lines.add(p)
    rays=sorted(tuple(s*c for c in v)for v in lines for s in(1,-1));base=functions.index(tuple(sorted(tuple(2*int(i==j)for j in range(4))for i in range(4))));report={'status':'EXACT_FINITE_GROUP_AND_FAN_INVENTORY','group_order':len(seen),'function_orbit_size':len(functions),'frames':frames,'frame_counts':[frameof.count(i)for i in range(len(frames))],'hyperplanes':sorted(walls),'rays':rays,'functions':functions,'frame_of_function':frameof,'base_function':base,'generators':generators,'group':sorted(seen),'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_f4_inventory.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('hyperplanes','rays','functions','group','generators','frame_of_function','frames')}));print('hyperplanes',len(walls),'rays',len(rays),'base',base)

if __name__=='__main__':main()
