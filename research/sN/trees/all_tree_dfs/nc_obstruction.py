#!/usr/bin/env python3
"""Certify a NC rank obstruction by formal right-kernel identities.

The modular augmented rank is an exact lower bound on rational rank. The
independent exact identities give an upper bound on the old rational rank.
Distinct free coordinates certify independence. Neither modular rank inclusion
nor a floating infeasibility report is treated as a real obstruction.
"""
import sys,json,gzip,time
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
from rational_identity import add,Verifier

def main():
    n=int(sys.argv[1]);here=Path(__file__).parent;path=here/f'nc_fast_{n}.json';start=time.time()
    with (path.open() if path.exists() else gzip.open(str(path)+'.gz','rt')) as f:d=json.load(f)
    witness=json.loads((here/f'nc_refined_{n}.json').read_text());free=witness['free_columns'];rels=witness['kernel_proposals']
    short=len(sys.argv)>2 and sys.argv[2]=='short'
    if short:rels=json.loads((here/f'nc_short_relations_{n}.json').read_text())['kernel_proposals']
    assert all(r is not None for r in rels)
    # Exact modular full rank of the free-coordinate projection is sufficient
    # for Q-linear independence of these rational vectors.
    P=witness['prime'];basis={}
    for r in rels:
        rr={i:Q(c) for i,c in r};row=[rr.get(f,Q(0)) for f in free]
        row=[c.numerator*pow(c.denominator,P-2,P)%P for c in row]
        for j,b in sorted(basis.items()):row=[(x-row[j]*y)%P for x,y in zip(row,b)]
        nz=[j for j,x in enumerate(row) if x];assert nz
        j=nz[0];iv=pow(row[j],P-2,P);basis[j]=[x*iv%P for x in row]
    assert len(basis)==len(rels)
    units=d['units'];orbits=d['orbits'];fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
    atoms={}
    used={i for r in rels for j,c in r for i in orbits[j]}
    for i in used:
        u=units[i];a=fs[u['apex']];den=[]
        for side,s in u['cuts']:
            q=tuple(sum(fs[v][j] for v in side) for j in range(n));den.extend([(q,1),(tuple(x+s*y for x,y in zip(q,a)),1)])
        atoms[i]=(tuple(-t for t in a),n-4,den)
    budget=900 if short else 300
    print('identities',len(rels),'distinct atoms',len(atoms),'budget',budget,flush=True)
    v=Verifier(budget);checked=[];status='UNRESOLVED'
    try:
        for j,r in enumerate(rels):
            expr=defaultdict(Q)
            for col,c in r:
                for i in orbits[col]:add(expr,Q(c),*atoms[i])
            ok=v.check(expr);checked.append(ok)
            print('IDENTITY',j,ok,'terms',len(expr),'calls',v.calls,'elapsed',time.time()-start,flush=True)
            if not ok:break
        if len(checked)==len(rels) and all(checked):
            assert len(orbits)-len(rels)<witness['modular_ranks'][1]
            status='EXACT_RANK_OBSTRUCTION'
    except TimeoutError:status='BUDGET_EXHAUSTED'
    out={'n':n,'status':status,'old_columns':len(orbits),'independent_exact_relations':sum(checked),
         'rational_rank_upper':len(orbits)-sum(checked),'modular_augmented_rank':witness['modular_ranks'][1],
         'elapsed_seconds':time.time()-start,'symbolic_calls':v.calls}
    name=f'nc_obstruction_{n}'+('_short' if short else '')
    (here/(name+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
if __name__=='__main__':main()
