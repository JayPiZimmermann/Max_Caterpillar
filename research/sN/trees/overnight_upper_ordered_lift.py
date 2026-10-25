#!/usr/bin/env python3
"""First coherent ordered-facet lift of the tetrahedron's one-paramid class.

At five labels, assign to each tetrahedral facet a combination of the six
parallelogram bases Delta_P-Delta_Q, |P|=|Q|=2. Exact cubical boundary
equations test whether only the noncrossing pair partitions suffice.
This is a chain-lifting test, not a new maximum width claim.
"""
from collections import defaultdict
from itertools import combinations,permutations
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
from flint import fmpq_mat

HERE=Path(__file__).parent


def difference(n,i,j):return tuple(int(k==i)-int(k==j) for k in range(n))
def plus(x,y):return tuple(a+b for a,b in zip(x,y))


def det3(columns):
    return sum((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))*
               columns[0][p[0]]*columns[1][p[1]]*columns[2][p[2]] for p in permutations(range(3)))


def cube(n,facet,pair):
    P=tuple(pair);Qp=tuple(v for v in facet if v not in P)
    h=difference(n,P[0],Qp[0]);a=difference(n,P[1],P[0]);b=difference(n,Qp[0],Qp[1])
    det=det3([[v[i] for i in facet[1:]] for v in (h,a,b)]);assert abs(det)==1
    coefficient=-det;edges=[]
    for v in (a,b):
        pos=v.index(1);neg=v.index(-1)
        if pos<neg:h=plus(h,v);v=tuple(-x for x in v);coefficient=-coefficient
        edges.append(v)
    if edges[0]>edges[1]:edges.reverse();coefficient=-coefficient
    a,b=edges;boundary=defaultdict(int)
    for base,edge,sign in ((plus(h,a),b,1),(h,b,-1),(plus(h,b),a,-1),(h,a,1)):
        boundary[(base,edge)]+=coefficient*sign
    return dict(h=h,edges=edges,coefficient=coefficient,P=P,Q=Qp),dict(boundary)


def crosses(e,f):
    a,b=sorted(e);c,d=sorted(f);return a<c<b<d or c<a<d<b


def system(noncrossing):
    n=5;columns=[];boundaries=[];keys=set()
    for missing in range(n):
        facet=tuple(v for v in range(n) if v!=missing)
        for pair in combinations(facet,2):
            other=tuple(v for v in facet if v not in pair)
            if noncrossing and crosses(pair,other):continue
            item,boundary=cube(n,facet,pair);item['missing']=missing
            boundary={key:(-1)**missing*c for key,c in boundary.items() if c}
            columns.append(item);boundaries.append(boundary);keys.update(boundary)
    keys=sorted(keys);rows=[[b.get(k,0) for b in boundaries]+[0] for k in keys]
    for missing in range(n):rows.append([int(c['missing']==missing) for c in columns]+[1])
    return columns,keys,rows


def main():
    records=[]
    for nc in (False,True):
        columns,keys,rows=system(nc)
        if not nc:
            assert all(sum(row[:-1])==6*row[-1] for row in rows),'Full symmetric lift must be a cycle'
            adjacency=[set() for _ in columns]
            for row in rows[:-5]:
                ids=[i for i,v in enumerate(row[:-1]) if v]
                assert len(ids)==2 and sorted(row[i] for i in ids)==[-1,1]
                adjacency[ids[0]].add(ids[1]);adjacency[ids[1]].add(ids[0])
            seen={0};pending=[0]
            while pending:
                for v in adjacency[pending.pop()]-seen:seen.add(v);pending.append(v)
            assert len(seen)==30 and len(keys)==60
        ordinary=fmpq_mat([r[:-1] for r in rows]).rank();augmented=fmpq_mat(rows).rank()
        record=dict(noncrossing_only=nc,columns=columns,segment_keys=keys,integer_rows=rows,ranks=[ordinary,augmented])
        if not nc:record['exchange_graph_check']=dict(vertices=len(seen),edges=len(keys),connected=True)
        if ordinary==augmented:
            rr,rank=fmpq_mat(rows).rref();cs=[Q(0)]*len(columns)
            for i in range(rank):
                p=next(j for j in range(len(columns)) if rr[i,j]);cs[p]=Q(str(rr[i,len(columns)]))
            assert all(sum(c*x for c,x in zip(cs,row[:-1]))==row[-1] for row in rows)
            record['coefficients']=list(map(str,cs));record['support']=sum(bool(c) for c in cs)
        records.append(record);print('NC',nc,'RANKS',record['ranks'],'SUPPORT',record.get('support'),flush=True)
    out=dict(status='EXACT_FIRST_ORDERED_CUBICAL_FACET_LIFT_TEST',records=records,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='Only the first 4-simplex boundary lift using the tetrahedron parallelogram bases Delta_P-Delta_Q. No all-dimensional lift or exponential count is asserted.')
    (HERE/'overnight_upper_ordered_lift.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
