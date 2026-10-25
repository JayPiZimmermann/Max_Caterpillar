#!/usr/bin/env python3
"""Normalized exterior cycle-space complex in adjacent-gap graph coordinates."""
from collections import defaultdict
from itertools import combinations,product
from pathlib import Path
import hashlib,json
from flint import fmpq_mat

HERE=Path(__file__).parent


def basis(q,k):
    edges=list(combinations(range(q),2))
    return [tuple(e) for e in combinations(edges,k)
            if {v for edge in e for v in edge}==set(range(q))]


def differential(q,graph):
    result=defaultdict(int)
    for split in range(q):
        factors=[]
        for u,v in graph:
            if u==split:
                factors.append([((split,v+1),1),((split+1,v+1),1)])
            elif v==split:
                factors.append([((u,split),1),((u,split+1),1)])
            else:
                factors.append([((u+int(u>split),v+int(v>split)),1)])
        for choices in product(*factors):
            edges=[e for e,_ in choices]
            if {v for edge in edges for v in edge}!=set(range(q+1)):continue
            if len(set(edges))!=len(edges):continue
            sign=(-1)**(split+1+sum(edges[i]>edges[j] for i in range(len(edges)) for j in range(i+1,len(edges))))
            result[tuple(sorted(edges))]+=sign
    return {g:c for g,c in result.items() if c}


def main():
    records=[]
    for k in (2,3,4):
        spaces={q:basis(q,k) for q in range(1,2*k+2)}
        matrices={}
        for q in range(1,2*k+1):
            source,target=spaces[q],spaces[q+1]
            columns=[differential(q,g) for g in source]
            matrix=fmpq_mat([[c.get(g,0) for c in columns] for g in target]) if target and source else None
            rank=matrix.rank() if matrix is not None else 0
            matrices[q]=(matrix,rank)
        for q in range(1,2*k):
            first,second=matrices[q][0],matrices[q+1][0]
            if first is not None and second is not None:
                assert all(not x for row in (second*first).tolist() for x in row)
        dimensions=[len(spaces[q]) for q in range(1,2*k+1)]
        ranks=[matrices[q][1] for q in range(1,2*k+1)]
        assert all((ranks[q-2] if q>=2 else 0)+ranks[q-1]==len(spaces[q])
                   for q in range(1,2*k+1)),('exactness',k)
        record=dict(exterior_degree=k,dimensions=dimensions,differential_ranks=ranks,
                    exact_in_every_normalized_degree=True)
        if k==2:
            matrix=matrices[3][0]
            record.update(source_graphs=spaces[3],target_graphs=spaces[4],
                          differential=[[str(v) for v in row] for row in matrix.tolist()],
                          inverse=[[str(v) for v in row] for row in matrix.inv().tolist()])
        records.append(record)
        print('NORMALIZED EXTERIOR',k,'DIM',dimensions,'RANKS',ranks,flush=True)
    result=dict(status='EXACT_NORMALIZED_GRAPH_COMPLEX_CONTROLS',records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Exact graph-model differential and acyclicity controls for exterior degrees2,3,4. The uniform EZ proof and quantitative homotopy still require a separate argument.')
    (HERE/'overnight_upper_ordered_normalized.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
