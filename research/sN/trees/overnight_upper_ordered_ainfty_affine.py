#!/usr/bin/env python3
"""Complete affine lower-gauge control for the two-page fifth primitive.

H2 is unique, H3 has one gauge, H4 has fifteen more. At the next equation
these parameters still enter linearly, so the domain here is exhaustive.
"""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,time
from flint import fmpq_mat
import overnight_upper_ordered_normalized as norm
import overnight_upper_ordered_ainfty_pages as pages

HERE=Path(__file__).parent

def add(*weighted):
    result=defaultdict(Q)
    for scale,chain in weighted:
        for g,c in chain.items():result[g]+=scale*c
    return pages.clean(result)

def solve_many(k,targets):
    source=[g for g in norm.basis(k+1,k) if pages.two_pages(g)]
    destination=norm.basis(k+2,k)
    columns=[norm.differential(k+1,g) for g in source]
    rows=[[c.get(g,0) for c in columns]+[str(t.get(g,0)) for t in targets] for g in destination]
    rr,rank=fmpq_mat(rows).rref()
    pivots=[next(j for j in range(len(source)+len(targets)) if rr[i,j]) for i in range(rank)]
    assert all(p<len(source) for p in pivots)
    solutions=[]
    for t in range(len(targets)):
        solution={source[p]:Q(str(rr[i,len(source)+t])) for i,p in enumerate(pivots) if rr[i,len(source)+t]}
        assert pages.delta(k+1,solution)==targets[t]
        solutions.append(solution)
    kernels=[]
    for free in sorted(set(range(len(source)))-set(pivots)):
        v={source[free]:Q(1)}
        for i,p in enumerate(pivots):
            if rr[i,free]:v[source[p]]=-Q(str(rr[i,free]))
        assert not pages.delta(k+1,v)
        kernels.append(v)
    return solutions,kernels,dict(k=k,columns=len(source),rank=rank,kernel_dimension=len(kernels))

def left(edge,chain):return pages.multiply(edge,chain,2)
def right(chain,edge,q):return pages.multiply(chain,edge,q)

def main():
    start=time.monotonic();E={((0,1),):Q(1)}
    H2,record2=pages.solve(2,{((0,1),(2,3)):Q(-1)})
    R3=add((-1,left(E,H2)),(1,right(H2,E,3)))
    (H3,),K3,record3=solve_many(3,[R3])
    assert len(K3)==1
    R4=add((-1,left(E,H3)),(1,pages.multiply(H2,H2,3)),(-1,right(H3,E,4)))
    R4var=[add((-1,left(E,k)),(-1,right(k,E,4))) for k in K3]
    solutions4,K4,record4=solve_many(4,[R4]+R4var)
    H4=solutions4[0]
    variations=[(k,lift) for k,lift in zip(K3,solutions4[1:])]+[({},k) for k in K4]
    assert len(variations)==16
    def fifth(h3,h4):
        return add((-1,left(E,h4)),(1,pages.multiply(H2,h3,3)),
                   (-1,pages.multiply(h3,H2,4)),(1,right(h4,E,5)))
    R5=fifth(H3,H4);V5=[fifth(a,b) for a,b in variations]
    assert not pages.delta(7,R5)
    assert all(not pages.delta(7,v) for v in V5)
    source=[g for g in norm.basis(6,5) if pages.two_pages(g)]
    destination=norm.basis(7,5)
    columns=[norm.differential(6,g) for g in source]
    # Solve delta H5 - sum t_i V_i = R5, including every earlier gauge.
    rows=[[c.get(g,0) for c in columns]+[str(-v.get(g,0)) for v in V5]+[str(R5.get(g,0))] for g in destination]
    rr,rank=fmpq_mat(rows).rref();variables=len(source)+len(V5)
    pivots=[next(j for j in range(variables+1) if rr[i,j]) for i in range(rank)]
    gap=variables in pivots
    result=dict(status='EXACT_COMPLETE_AFFINE_TWO_PAGE_FIFTH_PRIMITIVE_FAILURE' if gap else 'EXACT_COMPLETE_AFFINE_TWO_PAGE_FIFTH_PRIMITIVE',
        lower_records=[record2,record3,record4],lower_gauge_dimension=len(variations),
        fifth_source_columns=len(source),all_fifth_source_columns=len(norm.basis(6,5)),
        target_rows=len(destination),ranks=[rank-int(gap),rank],
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='The complete affine sequence of H3,H4 satisfying the specified consecutive-block higher identities, with every Hn supported on two-page normalized gap graphs. No statement about other geometric lifts follows.')
    if not gap:
        values=[Q(0)]*variables
        for i,p in enumerate(pivots):values[p]=Q(str(rr[i,variables]))
        gauges=values[len(source):]
        newH3=add((1,H3),*((t,a) for t,(a,b) in zip(gauges,variations)))
        newH4=add((1,H4),*((t,b) for t,(a,b) in zip(gauges,variations)))
        H5={g:c for g,c in zip(source,values) if c}
        assert pages.delta(4,newH3)==R3
        assert pages.delta(5,newH4)==add((-1,left(E,newH3)),(1,pages.multiply(H2,H2,3)),(-1,right(newH3,E,4)))
        assert pages.delta(6,H5)==fifth(newH3,newH4)
        result.update(gauges=list(map(str,gauges)),H2=pages.serialize(H2),H3=pages.serialize(newH3),
                      H4=pages.serialize(newH4),H5=pages.serialize(H5))
    else:
        # Exact dual witness in the full target space. This independently
        # certifies the gap without trusting a reported rank alone.
        dual_rows=[[column.get(g,0) for g in destination]+[0] for column in columns]
        dual_rows += [[str(v.get(g,0)) for g in destination]+[0] for v in V5]
        dual_rows += [[str(R5.get(g,0)) for g in destination]+[1]]
        dr,d_rank=fmpq_mat(dual_rows).rref();dual=[Q(0)]*len(destination)
        for i in range(d_rank):
            pivot=next(j for j in range(len(destination)+1) if dr[i,j])
            assert pivot<len(destination)
            dual[pivot]=Q(str(dr[i,len(destination)]))
        def pairing(chain):return sum(c*chain.get(g,0) for g,c in zip(destination,dual))
        assert all(pairing(c)==0 for c in columns)
        assert all(pairing(v)==0 for v in V5)
        assert pairing(R5)==1
        witness={g:c for g,c in zip(destination,dual) if c}
        result.update(separator=pages.serialize(witness),separator_terms=len(witness),
                      H2=pages.serialize(H2),H3=pages.serialize(H3),H4=pages.serialize(H4),
                      H3_kernel=[pages.serialize(v) for v in K3],
                      H4_lifts=[pages.serialize(v) for v in solutions4[1:]],
                      H4_kernel=[pages.serialize(v) for v in K4],
                      target=pages.serialize(R5))
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_ordered_ainfty_affine.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'RANKS',result['ranks'],'GAUGES',len(variations),
          'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
