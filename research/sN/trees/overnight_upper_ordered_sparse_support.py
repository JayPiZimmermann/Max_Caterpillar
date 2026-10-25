#!/usr/bin/env python3
"""Exact support controls for the normalized exterior graph contraction.

Checks every noncrossing cocycle against all noncrossing primitives at the
specified small exterior degrees. No restriction is placed on output rows.
"""
from itertools import combinations
from pathlib import Path
import hashlib,json,time
from flint import fmpq_mat
import overnight_upper_ordered_normalized as norm
import overnight_upper_ordered_sparse_homotopy as hom

HERE=Path(__file__).parent

def crosses(e,f):
    a,b=e;c,d=f
    return a<c<b<d or c<a<d<b

def nc(g):return not any(crosses(e,f) for e,f in combinations(g,2))

def kernel(matrix,ncols):
    if not matrix:return [[int(i==j) for i in range(ncols)] for j in range(ncols)]
    rr,rank=fmpq_mat(matrix).rref()
    pivots=[next(j for j in range(ncols) if rr[i,j]) for i in range(rank)]
    out=[]
    for free in sorted(set(range(ncols))-set(pivots)):
        v=[0]*ncols;v[free]=1
        for i,pivot in enumerate(pivots):v[pivot]=-rr[i,free]
        out.append(v)
    return out

def main():
    start=time.monotonic();records=[];first_crossing=None;first_obstruction=None
    for k in (2,3,4):
        for q in range(2,2*k+1):
            source=[g for g in norm.basis(q-1,k) if nc(g)]
            target=norm.basis(q,k)
            nc_target=[g for g in target if nc(g)]
            if not nc_target:continue
            next_basis=norm.basis(q+1,k)
            dc=[norm.differential(q,g) for g in nc_target]
            cycles=kernel([[c.get(g,0) for c in dc] for g in next_basis],len(nc_target))
            pc=[norm.differential(q-1,g) for g in source]
            rows=[[c.get(g,0) for c in pc] for g in target]
            rank=fmpq_mat(rows).rank() if source else 0
            cycle_columns=[{g:v for g,v in zip(nc_target,c) if v} for c in cycles]
            augmented=[row+[c.get(g,0) for c in cycle_columns] for row,g in zip(rows,target)]
            arank=fmpq_mat(augmented).rank() if source or cycles else 0
            record=dict(k=k,q=q,noncrossing_source=len(source),noncrossing_target=len(nc_target),
                        all_target=len(target),noncrossing_cycles=len(cycles),ranks=[rank,arank])
            records.append(record)
            print('NC COCYCLES',record,flush=True)
            if arank>rank and first_obstruction is None:
                for c in cycle_columns:
                    test=[row+[c.get(g,0)] for row,g in zip(rows,target)]
                    if fmpq_mat(test).rank()>rank:
                        first_obstruction=dict(k=k,q=q,source=source,target=target,
                            source_rows=rows,cocycle=[[g,str(v)] for g,v in c.items()],
                            ranks=[rank,rank+1])
                        # Independent exact dual witness, paired to one with c.
                        dual=fmpq_mat([[column.get(g,0) for g in target]+[0]
                                      for column in pc]+
                                     [[c.get(g,0) for g in target]+[1]])
                        rr,drank=dual.rref();separator=[0]*len(target)
                        for i in range(drank):
                            pivot=next(j for j in range(len(target)+1) if rr[i,j])
                            assert pivot<len(target)
                            separator[pivot]=rr[i,len(target)]
                        assert all(sum(w*column.get(g,0) for g,w in zip(target,separator))==0 for column in pc)
                        assert sum(w*c.get(g,0) for g,w in zip(target,separator))==1
                        first_obstruction['separator']=[[g,str(w)] for g,w in zip(target,separator) if w]
                        break
            if first_crossing is None:
                for g in nc_target:
                    for out,c in hom.graph_homotopy(q,g).items():
                        if not nc(out):
                            first_crossing=dict(k=k,q=q,input=g,output=out,coefficient=str(c))
                            break
                    if first_crossing:break
    result=dict(status='EXACT_NONCROSSING_COCYCLE_PRIMITIVE_TEST',records=records,
                first_crossing=first_crossing,first_obstruction=first_obstruction,
                seconds=time.monotonic()-start,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Only fixed adjacent-gap noncrossing support in the normalized graph complex; a failure is not a refutation of the original noncrossing geometric dictionary.')
    (HERE/'overnight_upper_ordered_sparse_support.json').write_text(json.dumps(result,indent=2)+'\n')
    print('COMPLETE',result['seconds'],'FIRST OBSTRUCTION',None if first_obstruction is None else (first_obstruction['k'],first_obstruction['q']),flush=True)

if __name__=='__main__':main()
