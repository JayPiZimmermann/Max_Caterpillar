#!/usr/bin/env python3
"""Exact completeness check for the smallest two-channel grafting relation."""
from collections import Counter,defaultdict
from pathlib import Path
import hashlib,json
from flint import fmpq_mat

HERE=Path(__file__).parent


def product_polynomial(forms):
    out={(0,0,0):1}
    for form in forms:
        new=defaultdict(int)
        for powers,c in out.items():
            for j,a in enumerate(form):
                if a:
                    q=list(powers);q[j]+=1;new[tuple(q)]+=c*a
        out=dict(new)
    return out


def main():
    x=(1,0,0);y=(0,1,0);s=(1,1,0)
    shift=lambda q,e:(q[0],q[1],e)
    denominator=[x,y,s]+[shift(q,e) for q in (x,y,s) for e in (-1,1)]
    keys=[];polys=[]
    for kind in 'SLR':
        for e in (1,-1):
            for f in (1,-1):
                q,r={'S':(x,y),'L':(s,x),'R':(s,y)}[kind]
                remaining=Counter(denominator);remaining.subtract([q,shift(q,e),r,shift(r,f)])
                assert min(remaining.values())>=0
                polys.append(product_polynomial(list(remaining.elements())));keys.append((kind,e,f))
    monomials=sorted({m for p in polys for m in p});rows=[[p.get(m,0) for p in polys] for m in monomials]
    relation=[0,-1,1,0,1,0,0,-1,-1,0,0,1]
    assert all(sum(x*y for x,y in zip(row,relation))==0 for row in rows)
    rank=fmpq_mat(rows).rank();assert rank==11
    out=dict(status='EXACT_UNIQUE_TWO_CHANNEL_LOCAL_RELATION',columns=keys,monomials=monomials,integer_rows=rows,
             rank=rank,nullity=1,relation=relation,denominator_linear_forms=denominator,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='All constant-coefficient identities among f_e(x)f_f(y), f_e(x+y)f_f(x), and f_e(x+y)f_f(y), where e,f=+-1 and f_e(q)=1/[q(q+e a)].')
    (HERE/'overnight_upper_interval_local.json').write_text(json.dumps(out,indent=2)+'\n')
    print(out['status'],'RANK',rank,'NULLITY',1)


if __name__=='__main__':main()
