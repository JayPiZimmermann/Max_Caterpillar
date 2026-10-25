#!/usr/bin/env python3
"""Independent positive-endpoint-cut and sequential-limit N5 check."""
from itertools import permutations
from pathlib import Path
import hashlib
import json
import sympy as S


def main():
    a,b,s,t=S.symbols('a b s t')
    frequencies=(a,s-a,t-a,b,a-b-s-t)
    units=[(1,((2,1),(3,2),(4,2))),
           (1,((1,2),(3,2),(4,2))),
           (2,((2,1),(3,2),(4,2)))]
    expected=[-12*(a*a-a*b+b*b)/(a*b*(a-b)*(a+b)*(2*a-b)),
              4*(12*a**4-14*a**3*b+13*a*a*b*b+2*a*b**3-b**4)
                /(a*b*(a-b)*(a+b)*(2*a-b)*(2*a+b)*(3*a-b)),
              8/(a*b*(a-b))]
    rows=[]
    for index,(root,edges)in enumerate(units):
        adjacency={v:[]for v in range(1,5)}
        for x,y in edges:adjacency[x].append(y);adjacency[y].append(x)
        positive_sides=[]
        for x,y in edges:
            side={x};queue=[x]
            while queue:
                v=queue.pop()
                for w in adjacency[v]:
                    if {v,w}=={x,y}or w in side:continue
                    side.add(w);queue.append(w)
            positive_sides.append(side)
        total=0
        outside_zero=0
        for permutation in permutations(range(5)):
            omega=[frequencies[i]for i in permutation]
            denominator=1
            for side in positive_sides:
                q=sum(omega[v]for v in side)+(omega[0]if root in side else 0)
                denominator*=q*(q+omega[0])
            kernel=-omega[0]/denominator
            first=S.cancel(s*kernel).subs(s,0)
            second=S.cancel(t*first).subs(t,0)
            assert not second.has(S.zoo,S.nan)
            if permutation[0]in(3,4):
                assert second==0
                outside_zero+=1
            total+=second
        total=S.factor(total)
        assert S.cancel(total-expected[index])==0
        rows.append(dict(unit_index=index,residue=str(total),outside_apex_terms_zero=outside_zero))
    # Triangular pole proof of independence, independent of a matrix rank.
    assert S.cancel((b+2*a)*expected[1]).subs(b,-2*a)!=0
    assert S.cancel((b+a)*expected[0]).subs(b,-a)!=0
    assert expected[2]!=0
    result=dict(status='INDEPENDENT_N5_DOUBLEWHEEL_CHECK_PASS',rows=rows,
                independence='unique poles b=-2a, then b=-a, then nonzero remaining function',
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='No producer import. Uses positive-endpoint components with a root-dependent head shift and actual successive rational limits, including all120 permutations per unit.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
