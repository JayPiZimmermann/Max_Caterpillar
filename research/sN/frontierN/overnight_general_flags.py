"""Exact support/sign relaxation of the singleton-diagonal-row cell condition.

For any real nonzero zero-sum row, a negative lexicographic point with coordinates
-B**priority_i has row sign opposite to sign(row_i) at its highest-priority
supported coordinate, for sufficiently large B.  Component indicators
of the active support hypergraph annihilate every active row.  Therefore each
component C imposes sum_{i in C} ell_i = 1_{winner in C}, independently of row
coefficient magnitudes.  A contradiction is uniform over that whole sign class.

This is a finite exact necessary-condition test, not a network existence test.
Single thread, no external dependencies. Output includes finite proof witnesses.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
import json
from pathlib import Path
import time

N = 5
FAMILIES = [((0,1),(0,2),(1,3),(2,4),(3,4)),
            ((0,1),(0,2),(0,3,4),(1,3),(2,4)),
            ((0,1),(0,2),(1,2,3),(1,2,4),(3,4))]

def components(fam, active):
    blocks = [{i} for i in range(N)]
    for j in active:
        s = set(fam[j])
        hit = [b for b in blocks if b & s]
        blocks = [b for b in blocks if not b & s]
        blocks.append(set().union(*hit))
    return [tuple(sorted(b)) for b in blocks]

def contradiction(constraints):
    piv = {}
    for idx, (mask, rhs, witness) in enumerate(constraints):
        row = [F(bool(mask & (1 << i))) for i in range(N)] + [F(rhs)]
        combo = {idx:F(1)}
        for k in range(N):
            if not row[k]: continue
            if k not in piv:
                q=row[k]; row=[z/q for z in row]
                combo={j:z/q for j,z in combo.items()}
                piv[k]=(row,combo); break
            q=row[k]; old,cert=piv[k]
            row=[a-q*b for a,b in zip(row,old)]
            for j,z in cert.items(): combo[j]=combo.get(j,F(0))-q*z
        else:
            if row[-1]:
                return [(str(v),constraints[j]) for j,v in combo.items() if v]
    return None

def run():
    started=time.monotonic(); result=[]
    flags=[(p,(-1,)*N) for p in permutations(range(N))]
    for fi,fam in enumerate(FAMILIES):
        choices=[[s for s in product((-1,1),repeat=len(sup)) if len(set(s))==2] for sup in fam]
        survivors=[]; certificates=[]
        for signs in product(*choices):
            seen={}; comps={}
            for perm,eps in flags:
                priority={v:k for k,v in enumerate(perm)}
                active=tuple(j for j,sup in enumerate(fam)
                    if signs[j][sup.index(max(sup,key=priority.get))]*eps[max(sup,key=priority.get)]>0)
                positives=[i for i in range(N) if eps[i]>0]
                winner=max(positives,key=priority.get) if positives else min(range(N),key=priority.get)
                if active not in comps: comps[active]=components(fam,active)
                for c in comps[active]:
                    mask=sum(1<<i for i in c); rhs=int(winner in c)
                    seen.setdefault((mask,rhs),(perm,eps,active,winner,c))
            constraints=[(mask,rhs,w) for (mask,rhs),w in sorted(seen.items())]
            cert=contradiction(constraints)
            if cert is None: survivors.append(signs)
            else: certificates.append({'signs':signs,'contradiction':cert})
        rec={'family':fam,'sign_classes':len(certificates)+len(survivors),
             'excluded':len(certificates),'survivors':survivors,'certificates':certificates}
        result.append(rec)
        print('family',fi,'classes',rec['sign_classes'],'excluded',rec['excluded'],
              'survivors',len(survivors),'seconds',round(time.monotonic()-started,3),flush=True)
    out={'description':__doc__,'N':N,'flag_type':'negative_lexicographic','results':result,'seconds':time.monotonic()-started}
    path=Path(__file__).with_suffix('.json'); path.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__': run()
