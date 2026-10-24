#!/usr/bin/env python3
"""Promote a modular upper-family rank obstruction using exact identities.

Compute the small right kernel modulo p, propose small integer relations, then
verify each as a formal rational-function identity by exact polynomial
arithmetic. An independent modular augmented rank plus sufficiently many
independent exact relations proves infeasibility over Q and R.
"""
import sys,json,time,math
from pathlib import Path
from fractions import Fraction
from collections import Counter
import numpy as np
import sympy as sp

def main():
    n=int(sys.argv[1]);des=int(sys.argv[2]);here=Path(__file__).parent
    d=json.loads((here/f'upper_fourier_{n}_desc{des}.json').read_text());P=d['prime'];m=len(d['units'])
    basis={};augmented={};start=time.time()
    def insert(v,b):
        v=np.array(v,dtype=np.int64)%P
        for j,w in sorted(b.items()):v=(v-v[j]*w)%P
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);b[j]=v*pow(int(v[j]),P-2,P)%P
    # Recompute every rational evaluation modulo p from the tree and frequency
    # data; the stored ranks and evaluations are not trusted inputs.
    for pt,row in zip(d['points'],d['rows']):
        check=[]
        for u in d['units']:
            a=pt[u['apex']];den=1
            for side,s in u['cuts']:
                q=sum(pt[i] for i in side);den=den*q*(q+s*a)%P
            assert den
            check.append(pow(-a,n-4,P)*pow(den,P-2,P)%P)
        prod=math.prod(pt)%P;assert prod
        check.append((-1)**(n-1)*pow(prod,P-2,P)%P)
        assert check==row
        insert(row,augmented)
    for row in d['rows']:
        v=np.array(row[:-1],dtype=np.int64)%P
        for j,b in sorted(basis.items()):v=(v-v[j]*b)%P
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);basis[j]=v*pow(int(v[j]),P-2,P)%P
    free=[j for j in range(m) if j not in basis];rels=[]
    assert [len(basis),len(augmented)]==d['ranks']
    for f in free:
        x=np.zeros(m,dtype=np.int64);x[f]=1
        for j,b in sorted(basis.items(),reverse=True):x[j]=-int(b@x)%P
        x=[int(t) if t<=P//2 else int(t)-P for t in x]
        rel=[(j,c) for j,c in enumerate(x) if c]
        print('relation',f,'support',len(rel),'maxcoef',max(abs(c) for j,c in rel),rel[:30],flush=True)
        rels.append(rel)
    zz=sp.symbols('z:'+str(n-1));freq=list(zz)+[-sum(zz)]
    def factors(u):
        numer=(-freq[u['apex']])**(n-4);fac=Counter();sign=1
        for side,s in u['cuts']:
            q=sum(freq[i] for i in side)
            for e in [q,q+s*freq[u['apex']]]:
                poly=sp.Poly(e,*zz)
                if poly.LC()<0:e=-e;sign=-sign
                fac[sp.expand(e)]+=1
        return sp.Poly(sign*numer,*zz),fac
    factored=[factors(u) for u in d['units']]
    verified=[]
    for k,rel in enumerate(rels):
        if max(abs(c) for j,c in rel)>1000:
            print('SKIP large coefficients',k,flush=True);continue
        common=Counter()
        for j,c in rel:common|=factored[j][1]
        total=sp.Poly(0,*zz)
        for j,c in rel:
            poly=c*factored[j][0]
            for e,power in (common-factored[j][1]).items():poly*=sp.Poly(e,*zz)**power
            total+=poly
        print('EXACT IDENTITY',k,total.is_zero,'elapsed',time.time()-start,flush=True)
        if total.is_zero:verified.append(rel)
    # The proposed vectors have distinct free coordinates, so their exact
    # independence is immediate and is checked here explicitly.
    assert all(dict(r).get(free[k],0)==1 and all(dict(r).get(free[l],0)==0 for l in range(len(free)) if l!=k) for k,r in enumerate(rels))
    out={'n':n,'descents':des,'columns':m,'modular_ranks':d['ranks'],'free_columns':free,'exact_relations':verified,
         'status':'EXACT_RANK_OBSTRUCTION' if m-len(verified)<d['ranks'][1] else 'UNRESOLVED',
         'elapsed_seconds':time.time()-start}
    (here/f'upper_rank_certificate_{n}_desc{des}.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',out['status'],flush=True)
if __name__=='__main__':main()
