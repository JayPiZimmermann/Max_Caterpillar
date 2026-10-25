#!/usr/bin/env python3
"""Exact ordered simplex recurrence with a concrete star-Koszul contraction.

Integer coefficients retain the common scalar product of (2^k-2).
The campaign is bounded; support measurements are not an asymptotic theorem.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib,json,sys,time
import overnight_upper_product_family as base
import overnight_upper_triangle_attachments as attachment
import overnight_upper_ordered_coherent as coherent

HERE=Path(__file__).parent


def add_term(out,head,edges,coefficient):
    if not coefficient or len(set(edges))!=len(edges):return
    coefficient*=(-1)**sum(edges[i]>edges[j] for i in range(len(edges)) for j in range(i+1,len(edges)))
    out[(head,tuple(sorted(edges)))]+=coefficient


@lru_cache(None)
def change_basis(n,edges,forward):
    """Forward: Eij -> zij+gj^-1 Ei-gj^-1 Ej. Reverse the triangular map."""
    factors=[]
    for kind,i,j in edges:
        zero=(0,)*(n-1)
        if forward:
            assert kind==2
            if j==0:
                factors.append(((zero,(0,i,0),1),))
            else:
                shift=tuple(-int(v==j) for v in range(1,n))
                factors.append(((zero,(1,i,j),1),(shift,(0,i,0),1),(shift,(0,j,0),-1)))
        else:
            if kind==0:
                factors.append(((zero,(2,i,0),1),))
            else:
                shift=tuple(-int(v==j) for v in range(1,n))
                factors.append(((zero,(2,i,j),1),(shift,(2,i,0),-1),(shift,(2,j,0),1)))
    out=defaultdict(int)
    for choices in product(*factors):
        head=tuple(sum(c[0][j] for c in choices) for j in range(n-1))
        add_term(out,head,[c[1] for c in choices],base_product(c[2] for c in choices))
    return coherent.clean(out)


def base_product(values):
    result=1
    for value in values:result*=value
    return result


def to_abstract(chain,n):
    out=defaultdict(int)
    for (head,edges),coefficient in chain.items():
        labels=[(2,e.index(1),e.index(-1)) for e in edges]
        add_term(out,head[1:],labels,int(coefficient))
    return coherent.clean(out)


def expand_basis(chain,n,forward):
    out=defaultdict(int)
    for (head,edges),coefficient in chain.items():
        for (shift,newedges),value in change_basis(n,edges,forward).items():
            out[(tuple(a+b for a,b in zip(head,shift)),newedges)]+=coefficient*value
    return coherent.clean(out)


def from_abstract(chain,n):
    out=defaultdict(int)
    for (head,edges),coefficient in chain.items():
        h=(-sum(head),)+head
        vectors=[base.diff(n,i,j) for _,i,j in edges]
        item=base.normalize_cube(h,vectors,coefficient)
        if item:out[item[0]]+=item[1]
    return coherent.clean(out)


def contract(chain,n):
    start=time.monotonic()
    original=to_abstract(chain,n)
    expanded=expand_basis(original,n,True)
    out=defaultdict(int)
    for (head,edges),coefficient in expanded.items():
        first_star=min((i for kind,i,_ in edges if kind==0),default=n)
        for j in range(1,first_star):
            exponent=head[j-1]
            powers=range(exponent) if exponent>=0 else range(exponent,0)
            sign=1 if exponent>=0 else -1
            for power in powers:
                h=(0,)*(j-1)+(power,)+head[j:]
                # Earlier star degrees vanish under augmentation, hence no
                # additional tensor-product sign occurs in these summands.
                out[(h,((0,j,0),)+edges)]+=sign*coefficient
    contracted=coherent.clean(out)
    answer=from_abstract(expand_basis(contracted,n,False),n)
    return answer,dict(input_cubes=len(chain),forward_basis_terms=len(expanded),
                       contracted_basis_terms=len(contracted),output_cubes=len(answer),
                       seconds=time.monotonic()-start)


def double(chain):
    out=defaultdict(int)
    for (head,edges),coefficient in chain.items():
        for bits in product((0,1),repeat=len(edges)):
            shifted=tuple(2*head[j]+sum(bit*edge[j] for bit,edge in zip(bits,edges)) for j in range(len(head)))
            out[(shifted,edges)]+=coefficient
    return coherent.clean(out)


def controls():
    # Chain contraction identity on augmentation-zero cycles independent of
    # the ordered simplex recurrence: translated triangular cycles.
    checks=0
    for n in (3,4,5):
        triangle=attachment.raw_chain(n,(((0,1,n-1),1,-1),))
        for shift in (base.diff(n,1,0),base.diff(n,n-1,1)):
            cycle=defaultdict(int)
            for (head,edges),coefficient in triangle.items():
                cycle[(base.addv(head,shift),edges)]+=coefficient
                cycle[(head,edges)]-=coefficient
            cycle=coherent.clean(cycle)
            fill,_=contract(cycle,n)
            assert coherent.boundary(fill)==cycle
            checks+=1
    return checks


def main():
    start=time.monotonic();checked=controls();records=[]
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X2={k:-v for k,v in triangle.items()}
    Y3=coherent.delta(X2,3)
    X,stats=contract(Y3,4)
    assert coherent.boundary(X)==Y3
    direct=coherent.multiply({((0,)*4,(base.diff(4,1,0),)):1},attachment.raw_chain(4,(((1,2,3),1,1),)))
    records.append(dict(simplex_dimension=3,target_scalar=1,contraction=stats,
                        equals_three_cube_base=X==direct,cubes=len(X)))
    scalar=1
    max_dimension=int(sys.argv[1]) if len(sys.argv)>1 else 6
    for dimension in range(4,max_dimension+1):
        labels=dimension+1;k=dimension-2
        boundary=coherent.delta(X,dimension)
        assert not coherent.boundary(boundary),'coherent ordered cycle'
        corrected=defaultdict(int,{key:2**k*value for key,value in boundary.items()})
        for key,value in double(boundary).items():corrected[key]-=value
        corrected=coherent.clean(corrected)
        assert not coherent.augmentation(corrected)
        assert not coherent.boundary(corrected)
        print('ORDERED FILL INPUT',dimension,'OLD',len(X),'FACET',len(boundary),
              'CORRECTED',len(corrected),'SECONDS',time.monotonic()-start,flush=True)
        if len(corrected)>200000 or time.monotonic()-start>300:
            records.append(dict(simplex_dimension=dimension,status='PREDECLARED_SUPPORT_OR_TIME_STOP',
                                facet_cubes=len(boundary),corrected_cubes=len(corrected)))
            break
        X,stats=contract(corrected,labels)
        assert coherent.boundary(X)==corrected,'full integer cubical filling identity'
        scalar*=2**k-2
        record=dict(simplex_dimension=dimension,target_scalar=scalar,cubes=len(X),
                    facet_cubes=len(boundary),corrected_cubes=len(corrected),contraction=stats,
                    max_head_l1=max(sum(abs(x) for x in head[1:]) for head,_ in X),
                    max_coefficient_bits=max(abs(int(c)).bit_length() for c in X.values()))
        records.append(record)
        print('ORDERED FILL COMPLETE',record,'SECONDS',time.monotonic()-start,flush=True)
    result=dict(status='EXACT_ORDERED_CUBICAL_RECURRENCE_CONTROLS',records=records,
                independent_translated_cycle_controls=checked,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start,
                scope='Every completed recurrence equality is checked as an exact integer cubical chain. Support measurements do not prove an exponential width bound.')
    (HERE/'overnight_upper_ordered_contraction.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',len(records),'SECONDS',result['seconds'],flush=True)


if __name__=='__main__':main()
