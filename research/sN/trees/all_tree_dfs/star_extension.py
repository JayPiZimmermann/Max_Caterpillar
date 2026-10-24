#!/usr/bin/env python3
"""Check adding the omitted empty-cut rooted stars to an upper family.
Modular proposal only; positive output must pass the exact rational gate.
"""
import sys,json,time,math,gzip
from pathlib import Path
from flint import nmod_mat
from nc_claw_extend import evaluator
from nc_top import key,ratrec

n=int(sys.argv[1]);mode=sys.argv[2];here=Path(__file__).parent;start=time.time()
path=here/(f'nc_fast_{n}.json' if mode=='nc' else f'upper_fourier_{n}_desc1.json')
with (path.open() if path.exists() else gzip.open(str(path)+'.gz','rt')) as f:d=json.load(f)
oldorbits=d['orbits'] if mode=='nc' else [[i] for i in range(len(d['units']))]
rows=d['rows'];pts=d['points'];P=d['prime']
if mode=='nc':
    extra=json.loads((here/f'nc_refined_{n}.json').read_text())['extra_points'];ev=evaluator(d['units'],oldorbits,n)
    for pt in extra:rows.append(ev(pt)+[(-1)**(n-1)*pow(math.prod(pt)%P,P-2,P)%P])
    pts+=extra
units=[]
for a in range(n):
    for c in range(n):
        if c==a:continue
        units.append({'apex':a,'root':c,'edges':[(c,v) for v in range(n) if v not in (a,c)],
                      'cuts':[((v,),-1) for v in range(n) if v not in (a,c)]})
if mode=='nc':
    idx={key(u,n):i for i,u in enumerate(units)};seen=set();orbits=[]
    for i,u in enumerate(units):
        if i in seen:continue
        o={idx[key(u,n,[(sg*j+b)%n for j in range(n)])] for sg in (-1,1) for b in range(n)}
        seen|=o;orbits.append(sorted(o))
else:orbits=[[i] for i in range(len(units))]
ev=evaluator(units,orbits,n)
for j,pt in enumerate(pts):rows[j]=rows[j][:-1]+ev(pt)+[rows[j][-1]]
m=len(rows[0])-1;print('RREF',len(rows),m+1,'extra',len(orbits),flush=True)
M=nmod_mat(rows,P);R,rank=M.rref(inplace=True);piv=[next(j for j in range(m+1) if R[i,j]) for i in range(rank)]
out={'n':n,'mode':mode,'old_columns':len(oldorbits),'new_units':units,'new_orbits':orbits,
     'modular_ranks':[rank-int(m in piv),rank],'status':'MODULAR_DIAGNOSTIC_ONLY'}
if m in piv and n<=6:
    free=[j for j in range(m) if j not in piv];rels=[]
    for f in free:
        rel=[(f,'1')]
        for i,j in enumerate(piv):
            if j==m:continue
            a=-int(R[i,f])%P
            if a:
                c=ratrec(a,P);assert c is not None;rel.append((j,str(c)))
        rels.append(rel)
    out['free_columns']=free;out['kernel_proposals']=rels
if m not in piv:
    x=[0]*m
    for i,j in enumerate(piv):x[j]=int(R[i,m])
    cs=[ratrec(a,P) for a in x]
    if all(c is not None for c in cs):out['coefficient_proposal']=[str(c) for c in cs]
out['elapsed_seconds']=time.time()-start
(here/f'star_extension_{n}_{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',out['modular_ranks'],'proposal','coefficient_proposal' in out,'elapsed',time.time()-start,flush=True)
