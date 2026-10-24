"""Exact rational cut-peeling refinement for six-row cell-condition survivors.

If ell(C)=1_{a in C} is forced globally, and exactly one surviving active row
crosses C with a provably nonzero coefficient sum on C, its coefficient in a
representation of e_a-ell must vanish. Remove it from that cell, recompute
components, and iterate. Nonzero cut sum is guaranteed when all coefficients
on either side of the cut have one strict sign. No magnitude grid is used.

This is a diagnostic producer until an independent finite checker is supplied.
"""
from fractions import Fraction as F
from itertools import permutations,product
from pathlib import Path
import json,time

BASE=Path(__file__).with_suffix('')

def solve(bits):
    piv={}
    while bits:
        b=bits&-bits;k=b.bit_length()-1;bits-=b
        mask=k//2+1;rhs=k%2;r=[F(bool(mask>>i&1)) for i in range(5)]+[F(rhs)]
        for i in range(5):
            if not r[i]:continue
            if i not in piv:
                q=r[i];piv[i]=[x/q for x in r];break
            q=r[i];r=[x-q*y for x,y in zip(r,piv[i])]
        else:
            if r[-1]:return None
    fixed={}
    for mask in range(1,32):
        r=[F(bool(mask>>i&1)) for i in range(5)]+[F(0)]
        for i in range(5):
            if r[i] and i in piv:
                q=r[i];r=[x-q*y for x,y in zip(r,piv[i])]
        if not any(r[:5]):fixed[mask]=-r[-1]
    return fixed

def prep(fam):
    comps=[]
    for active in range(64):
        blocks=[{i} for i in range(5)]
        for j,sup in enumerate(fam):
            if not(active>>j&1):continue
            s=set(sup);hit=[b for b in blocks if b&s]
            blocks=[b for b in blocks if not b&s]+[set().union(*hit)]
        masks=[sum(1<<i for i in b) for b in blocks]
        comps.append([sum(1<<(2*(m-1)+int(bool(m>>a&1))) for m in masks) for a in range(5)])
    flags=[]
    for p in permutations(range(5)):
        rank={v:k for k,v in enumerate(p)};leaders=[sup.index(max(sup,key=rank.get)) for sup in fam]
        for eps in product((-1,1),repeat=5):
            signs=[eps[sup[k]] for sup,k in zip(fam,leaders)]
            winner=max(range(5),key=lambda i:eps[i]*2**rank[i])
            flags.append((leaders,signs,winner))
    return comps,flags

def run_profile(fam,signs,comps,flags):
    cells=set()
    for lead,eps,a in flags:
        active=sum(1<<j for j,k in enumerate(lead) if signs[j][k]*eps[j]>0)
        cells.add((active,a))
    cuts={}
    for C in range(1,32):
        crossing=nonzero=0
        for j,(sup,sgn) in enumerate(zip(fam,signs)):
            inside=[sgn[k] for k,i in enumerate(sup) if C>>i&1]
            outside=[sgn[k] for k,i in enumerate(sup) if not(C>>i&1)]
            if not inside or not outside:continue
            crossing|=1<<j
            if len(set(inside))==1 or len(set(outside))==1:nonzero|=1<<j
        cuts[C]=(crossing,nonzero)
    bits=0
    for active,a in cells:bits|=comps[active][a]
    rounds=removed=0
    while True:
        fixed=solve(bits)
        if fixed is None:return {'survives':False,'rounds':rounds,'removed':removed}
        rounds+=1;changed=False;newcells=set()
        for active,a in cells:
            old=active
            while True:
                last=active
                for C,value in fixed.items():
                    if value!=int(bool(C>>a&1)):continue
                    crossing,nonzero=cuts[C];one=active&crossing
                    if one and one&(one-1)==0 and one&nonzero:active^=one;removed+=1
                if last==active:break
            changed |=old!=active
            newcells.add((active,a));bits|=comps[active][a]
        cells=newcells
        if not changed:return {'survives':True,'rounds':rounds,'removed':removed,
            'fixed_sums':{str(k):str(v) for k,v in fixed.items()}}

def main():
    start=time.monotonic();source=json.loads(Path(__file__).with_name('overnight_general_six_full.json').read_text())
    out={'status':'Exact rational diagnostic, independent checker pending','completed':[]}
    for rec in source['completed']:
        if not rec['survivors']:continue
        fam=rec['family'];comps,flags=prep(fam);survivors=[];excluded=0;rounds=0
        for signs in rec['survivors']:
            result=run_profile(fam,signs,comps,flags);rounds=max(rounds,result['rounds'])
            if result['survives']:survivors.append({'signs':signs,'result':result})
            else:excluded+=1
        r={'family_index':rec['family_index'],'family':fam,'tested':len(rec['survivors']),
           'excluded':excluded,'survivors':survivors,'max_rounds':rounds}
        out['completed'].append(r);out['seconds']=time.monotonic()-start
        BASE.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
        print('family',rec['family_index'],'tested',r['tested'],'survivors',len(survivors),'rounds',rounds,flush=True)

if __name__=='__main__':main()
