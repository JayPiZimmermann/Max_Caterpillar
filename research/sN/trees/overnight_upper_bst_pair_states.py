#!/usr/bin/env python3
"""Necessary iterated-pole control for orientation-averaged coupled BST states.

A passing case is only an admissibility control, not a geometric realization.
An explicit repeated pole in dimension >=2 is an exact CPWL obstruction.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib,json,time
import sympy as sp

HERE=Path(__file__).parent


@lru_cache(None)
def trees(labels):
    if not labels:
        return ((None,()),)
    result=[]
    for j,root in enumerate(labels):
        for lr,le in trees(labels[:j]):
            for rr,re in trees(labels[j+1:]):
                edges=list(le+re)
                if lr is not None:edges.append((root,lr))
                if rr is not None:edges.append((root,rr))
                result.append((root,tuple(sorted(edges))))
    return tuple(result)


def cuts(root,edges):
    children={v:[] for e in edges for v in e}
    for u,v in edges:children[u].append(v)
    def descendants(v):
        result={v}
        for w in children[v]:result.update(descendants(w))
        return result
    return [descendants(v) for _,v in edges]


def expression(n,first,second,character):
    root,edges=first
    assert root==second[0]
    a,*coordinates=sp.symbols('a:'+str(n))
    nonroot=[v for v in range(n) if v!=root]
    omega=dict(zip(nonroot,coordinates))
    omega[root]=-a-sum(coordinates)
    firstcuts=cuts(root,edges)
    secondcuts=cuts(*second)
    unshifted=sp.prod(sum(omega[v] for v in cut) for cut in firstcuts)
    total=0
    for signs in product((-1,1),repeat=n-1):
        degree=[0]*n
        for (parent,child),sign in zip(edges,signs):
            degree[child]+=sign;degree[parent]-=sign
        shifted=sp.prod(sum(omega[v]+a*degree[v] for v in cut) for cut in secondcuts)
        weight=1 if character=='plain' else sp.prod(signs)
        total+=weight*(-a)**(n-3)/(unshifted*shifted)
    return sp.factor(total),tuple([a]+coordinates)


def pole_check(expression,variables,deadline,trace=(),cache=None):
    if time.monotonic()>deadline:raise TimeoutError
    if cache is None:cache=set()
    expression=sp.cancel(expression)
    if expression==0:return None,1
    if len(variables)<2:return None,1
    key=(expression,variables)
    if key in cache:return None,0
    cache.add(key)
    numerator,denominator=sp.fraction(expression)
    _,factors=sp.factor_list(denominator,*variables)
    if any(sp.Poly(f,*variables).total_degree()!=1 for f,_ in factors):
        raise AssertionError('Only rational linear poles are allowed')
    repeated=[(f,p) for f,p in factors if p>1]
    if repeated:
        return dict(trace=list(trace),dimension=len(variables),
                    expression=str(sp.factor(expression)),
                    repeated_factor=str(repeated[0][0]),order=int(repeated[0][1])),1
    checked=1
    if len(variables)==2:return None,checked
    for factor,_ in factors:
        pivot=next(v for v in variables if sp.diff(factor,v)!=0)
        coefficient=sp.diff(factor,pivot)
        value=-factor.subs(pivot,0)/coefficient
        # This is the algebraic residue with local defining form factor.
        residue=sp.cancel(expression*factor).subs(pivot,value)
        remaining=tuple(v for v in variables if v!=pivot)
        failure,count=pole_check(residue,remaining,deadline,trace+(str(factor),),cache)
        checked+=count
        if failure:return failure,checked
    return None,checked


def main():
    start=time.monotonic();records=[]
    # All pairs of three-vertex BSTs with the same root; then every pair at
    # four vertices until a failure or the bounded campaign deadline.
    stop=False
    for n in (3,4):
        ts=trees(tuple(range(n)))
        for first in ts:
            for second in ts:
                if first[0]!=second[0] or first==second:continue
                for character in ('plain','signed'):
                    expr,variables=expression(n,first,second,character)
                    try:
                        failure,count=pole_check(expr,variables,min(start+160,time.monotonic()+25))
                    except TimeoutError:
                        records.append(dict(n=n,first=first,second=second,character=character,
                                            status='POLE_CONTROL_BUDGET_STOP'))
                        stop=True;break
                    record=dict(n=n,first=first,second=second,character=character,
                                status='EXACT_NON_CPWL_ITERATED_POLE' if failure else 'NECESSARY_ITERATED_POLE_CONTROL_PASS',
                                visited_states=count,failure=failure)
                    records.append(record)
                    print('BST PAIR',n,first,second,character,record['status'],count,
                          'SECONDS',time.monotonic()-start,flush=True)
                    if failure:
                        stop=True
                if stop:break
            if stop:break
        if stop:break
    result=dict(status='BOUNDED_COUPLED_BST_GEOMETRIC_ADMISSIBILITY_CONTROLS',
                records=records,seconds=time.monotonic()-start,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='A failure is an exact necessary CPWL-pole obstruction. Passing all tested flags is not a sufficiency theorem or a paramid representation.')
    (HERE/'overnight_upper_bst_pair_states.json').write_text(json.dumps(result,indent=2)+'\n')
    print('COMPLETE',len(records),'SECONDS',result['seconds'],flush=True)


if __name__=='__main__':main()
