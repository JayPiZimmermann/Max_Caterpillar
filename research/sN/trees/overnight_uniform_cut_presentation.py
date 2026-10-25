#!/usr/bin/env python3
"""Exact integer common-denominator checks for the charged root-slide defect."""
from collections import Counter,defaultdict
from pathlib import Path
import hashlib,json,time


def polynomial(forms):
    p={(0,0,0):1}
    for form in forms:
        q=defaultdict(int)
        for monomial,c in p.items():
            for j,coefficient in enumerate(form):
                if coefficient:
                    m=list(monomial);m[j]+=1;q[tuple(m)]+=c*coefficient
        p={m:c for m,c in q.items()if c}
    return p


def add(total,p,weight=1):
    for m,c in p.items():total[m]+=weight*c


def main():
    started=time.monotonic();x=(1,0,0);y=(0,1,0);q=(1,1,0)
    shift=lambda f,e:(f[0],f[1],e)
    first=defaultdict(int)
    add(first,polynomial([y,shift(y,-1)]))
    add(first,polynomial([x,shift(x,-1)]),-1)
    add(first,polynomial([(-1,1,0),shift(q,-1)]),-1)
    assert not any(first.values())
    factors=[x,y,q]+[shift(f,e)for f in(x,y,q)for e in(-1,1)]
    # left side minus right side of the displayed triangular correction.
    specifications=[(1,[(q,-1),(x,-1)]),(-1,[(q,-1),(y,-1)]),
                    (-1,[(q,1),(x,1)]),(1,[(q,1),(y,1)]),
                    (1,[(x,1),(y,-1)]),(-1,[(x,-1),(y,1)])]
    total=defaultdict(int)
    for coefficient,pairs in specifications:
        remaining=Counter(factors)
        for f,e in pairs:remaining.subtract([f,shift(f,e)])
        assert min(remaining.values())>=0
        add(total,polynomial(list(remaining.elements())),coefficient)
    assert not any(total.values())
    data=dict(status='EXACT_CHARGED_ROOT_SLIDE_AND_TRIANGULAR_CORRECTION_PASS',
              defect_numerator_zero=True,six_term_numerator_zero=True,
              seconds=time.monotonic()-started,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Local rational identities only. No assertion that these relations present the full canonical kernel space or preserve every outward-twin relation.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data,indent=2))


if __name__=='__main__':main()
