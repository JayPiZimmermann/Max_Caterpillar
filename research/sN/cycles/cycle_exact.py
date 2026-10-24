#!/usr/bin/env python3
"""Certify fixed-cycle obstruction using exact Q identities and rank lower bound.
Budget 180 s. Uses the already independently controlled tree atom formula.
"""
import sys,json,math,time,hashlib
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
from flint import nmod_mat,fmpz_mat
from cycle_fourier import family,cuts
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'trees/all_tree_dfs'))
from nc_top import ratrec
from rational_identity import add,Verifier
n=int(sys.argv[1]);here=Path(__file__).parent;src=here/f'cycle_probe_{n}.json';d=json.loads(src.read_text());P=d['prime'];m=len(d['orbits']);start=time.time()
ff=family(n);keys=list(ff)
assert [[list(h),[list(e) for e in es]] for h,es in keys]==d['keys']
# Recompute every stored modular row, directly with integer arithmetic.
rows=[]
for om in d['points']:
    vv=[]
    for k in keys:
        a,atoms=ff[k];v=0
        for atom in atoms:
            den=1
            for side,H in cuts(atom,a):
                q=sum(om[i] for i in side);den=den*(q+om[a]*H)*(q+om[a]*(H+1))%P
            assert den
            v=(v+pow(-om[a],n-4,P)*pow(den,P-2,P))%P
        vv.append(v)
    row=[sum(vv[j] for j in orb)%P for orb in d['orbits']]
    row.append((-1)**(n-1)*pow(math.prod(om)%P,P-2,P)%P);rows.append(row)
assert rows==d['rows']
R,rank=nmod_mat(rows,P).rref();piv=[next(j for j in range(m+1) if R[i,j]) for i in range(rank)]
free=[j for j in range(m) if j not in piv];rels=[]
for f in free:
    rr=[Q(0)]*m;rr[f]=1
    for i,j in enumerate(piv):
        if j<m:rr[j]=ratrec(-int(R[i,f])%P,P);assert rr[j] is not None
    den=math.lcm(*(x.denominator for x in rr));rels.append([int(x*den) for x in rr])
L,T=fmpz_mat(rels).lll(transform=True);assert T*fmpz_mat(rels)==L and abs(T.det())==1
F=fmpz_mat([[L[i,j] for j in free] for i in range(len(rels))]);assert F.det()
fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
expressions=[]
for orb in d['orbits']:
    expr=defaultdict(Q)
    for i in orb:
        a,atoms=ff[keys[i]];af=fs[a]
        for atom in atoms:
            den=[]
            for side,H in cuts(atom,a):
                q=tuple(sum(fs[v][j] for v in side) for j in range(n))
                den.extend((tuple(x+t*y for x,y in zip(q,af)),1) for t in (H,H+1))
            add(expr,1,tuple(-x for x in af),n-4,den)
    expressions.append(expr)
v=Verifier(180);checked=[];record=[]
for i in range(len(rels)):
    expr=defaultdict(Q);r=[]
    for j in range(m):
        if not L[i,j]:continue
        c=Q(int(L[i,j]));r.append((j,str(c)))
        for t,a in expressions[j].items():expr[t]+=c*a
    ok=v.check(expr);checked.append(ok);record.append(r)
    print('IDENTITY',i,ok,'terms',sum(bool(x) for x in expr.values()),'sec',time.time()-start,flush=True)
    assert ok
assert m-len(rels)<rank
out=dict(n=n,status='EXACT_RANK_OBSTRUCTION',domain='fixed cycle on all nonapex labels; canonical root, arbitrary orientations and all face states',columns=m,rational_rank_upper=m-len(rels),modular_augmented_rank=rank,prime=P,independent_exact_relations=len(rels),free_projection_determinant=str(F.det()),relations=record,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),elapsed_seconds=time.time()-start)
(here/f'cycle_obstruction_{n}.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],out['rational_rank_upper'],rank,flush=True)
