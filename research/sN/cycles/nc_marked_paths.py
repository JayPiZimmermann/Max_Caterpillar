#!/usr/bin/env python3
"""NC8: add arbitrary source/root markings of noncrossing paths.
Budget480 s after the timed-out180 s instrument run; direct FLINT storage avoids Python matrix memory duplication.
"""
import sys,json,gzip,itertools,time,math,random
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'trees/all_tree_dfs'))
from nc_top import key,ratrec
from nc_claw_extend import evaluator
from flint import nmod_mat
HERE=Path(__file__).parent;OLD=HERE.parent/'trees/all_tree_dfs';start=time.time();n=8;P=1000003
# Metadata-only prefix: the old numeric matrix is deliberately not loaded.
with gzip.open(OLD/'nc_fast_8.json.gz','rt') as f:
    parts=[]
    for line in f:
        if line.startswith('  "points":'):break
        parts.append(line)
d=json.loads(''.join(parts).rstrip().rstrip(',')+'\n}')
units=d['units'];oldkeys={key(u,n) for u in units};out={key(u,n):u for u in units};paths=[]
for p in itertools.permutations(range(n-1)):
    if p[0]>p[-1]:continue
    es=list(zip(p,p[1:]));ss=[sorted(e) for e in es]
    if any(a<c<b<e or c<a<e<b for a,b in ss for c,e in ss):continue
    paths.append(p)
for p in paths:
    for spos in range(n-1):
        es=[(p[j+1],p[j]) if j<spos else (p[j],p[j+1]) for j in range(n-2)]
        for rpos in range(spos,n-1):
            for apex in range(n):
                lab=[i for i in range(n) if i!=apex];ee=[(lab[u],lab[v]) for u,v in es]
                u=dict(apex=apex,source=lab[p[spos]],root=lab[p[rpos]],edges=ee);kk=key(u,n)
                if kk in out:continue
                cs=[]
                for j,(x,y) in enumerate(ee):
                    side={lab[z] for z in p[:j+1]};sgn=1 if x in side else -1
                    if u['root'] in side:side=set(lab)-side;sgn=-sgn
                    cs.append((sorted(side),sgn))
                u['cuts']=cs;out[kk]=u
units=list(out.values());index={key(u,n):j for j,u in enumerate(units)};seen=set();orbits=[]
for i,u in enumerate(units):
    if i in seen:continue
    orb=sorted({index[key(u,n,[(sg*j+a)%n for j in range(n)])] for sg in(-1,1) for a in range(n)})
    seen.update(orb);orbits.append(orb)
print('paths',len(paths),'units',len(units),'added',len(units)-len(oldkeys),'orbits',len(orbits),'sec',time.time()-start,flush=True)
(HERE/'nc_marked_paths_8_family.json').write_text(json.dumps(dict(units=units,orbits=orbits)))
print('metadata saved',time.time()-start,flush=True)
m=len(orbits);nr=m+30;M=nmod_mat(nr,m+1,P);print('matrix allocated',time.time()-start,flush=True)
ev=evaluator(units,orbits);print('evaluator initialized',time.time()-start,flush=True)
rng=random.Random(24102412);pts=[]
for j in range(nr):
    pp=[rng.randint(1,5)]
    for _ in range(n-2):pp.append(sum(pp)+rng.randint(1,10))
    pt=[-sum(pp)]+pp;rng.shuffle(pt);row=ev(pt)+[(-1)**(n-1)*pow(math.prod(pt)%P,P-2,P)%P];pts.append(pt)
    for k,v in enumerate(row):M[j,k]=v
    if (j+1)%100==0:print('rows',j+1,'sec',time.time()-start,flush=True)
    if time.time()-start>420:
        (HERE/'nc_marked_paths_8_budget.json').write_text(json.dumps(dict(status='BUDGET_EXHAUSTED',rows=j+1,seconds=time.time()-start)))
        raise TimeoutError('generation budget')
print('RREF',nr,m+1,'sec',time.time()-start,flush=True);R,rank=M.rref(inplace=True)
piv=[next(j for j in range(m+1) if R[i,j]) for i in range(rank)]
res=dict(n=n,prime=P,seed=24102412,status='MODULAR_DIAGNOSTIC_ONLY',family='old NC caterpillars + all NC source/root paths',units=len(units),orbits=m,rows=nr,ranks=[rank-int(m in piv),rank],elapsed_seconds=time.time()-start)
if m not in piv:
    x=[0]*m
    for i,j in enumerate(piv):x[j]=int(R[i,m])
    cs=[ratrec(a,P) for a in x];res['rational_reconstructed']=sum(c is not None for c in cs)
    if all(c is not None for c in cs):res['coefficient_proposal']=[str(c) for c in cs]
    (HERE/'nc_marked_paths_8_family.json').write_text(json.dumps(dict(units=units,orbits=orbits,points=pts)))
(HERE/'nc_marked_paths_8.json').write_text(json.dumps(res,indent=2)+'\n');print(res,flush=True)
