#!/usr/bin/env python3
"""Repair the first ordered facet lift using explicit head-exchange kernels."""
from collections import defaultdict
from itertools import product
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,time
from flint import fmpq_mat
from overnight_upper_ordered_lift import cube,difference,plus,det3,crosses
from overnight_upper_interval_states import pruefer

HERE=Path(__file__).parent


def normalized_cube(facet,h,edges):
    coefficient=det3([[v[i] for i in facet[1:]] for v in [h]+edges]);assert abs(coefficient)==1
    out=[]
    for v in edges:
        if v.index(1)<v.index(-1):h=plus(h,v);v=tuple(-x for x in v);coefficient=-coefficient
        out.append(v)
    if out[0]>out[1]:out.reverse();coefficient=-coefficient
    return (h,tuple(out)),coefficient


def boundary(chain):
    out=defaultdict(Q)
    for (h,(a,b)),coefficient in chain.items():
        for base,edge,sign in ((plus(h,a),b,1),(h,b,-1),(plus(h,b),a,-1),(h,a,1)):
            out[(base,edge)]+=coefficient*sign
    return {k:v for k,v in out.items() if v}


def is_nc(key):
    edges=[tuple(i for i,x in enumerate(v) if x) for v in key[1]]
    return not crosses(*edges)


def main():
    started=time.monotonic();baseline=defaultdict(Q);relations=[];witnesses=[]
    for missing in range(5):
        facet=tuple(v for v in range(5) if v!=missing);item,_=cube(5,facet,facet[:2])
        baseline[(tuple(item['h']),tuple(item['edges']))]+=(-1)**missing*item['coefficient']
        seen=set()
        for local in pruefer(4):
            tree=tuple(sorted(tuple(sorted((facet[u],facet[v]))) for u,v in local))
            for bits in product((1,-1),repeat=3):
                forms=[difference(5,u,v) if sign==1 else difference(5,v,u) for (u,v),sign in zip(tree,bits)]
                relation=defaultdict(Q)
                for head in range(3):
                    key,c=normalized_cube(facet,forms[head],[forms[j] for j in range(3) if j!=head])
                    relation[key]+=(-1)**missing*c
                relation={k:v for k,v in relation.items() if v};signature=tuple(sorted(relation.items()))
                if signature in seen:continue
                seen.add(signature);relations.append(relation);witnesses.append(dict(missing=missing,tree=tree,orientations=bits))
    bd0=boundary(baseline);bds=[boundary(r) for r in relations]
    segments=sorted(set(bd0)|{k for bd in bds for k in bd})
    bad=sorted({k for r in relations for k in r if not is_nc(k)}|{k for k in baseline if not is_nc(k)})
    rows=[[bd.get(k,Q(0)) for bd in bds]+[-bd0.get(k,Q(0))] for k in segments]
    rows += [[r.get(k,Q(0)) for r in relations]+[-baseline.get(k,Q(0))] for k in bad]
    integer_rows=[[int(v) for v in row] for row in rows]
    print('SYSTEM',len(relations),'RELATIONS',len(segments),'SEGMENTS',len(bad),'FORBIDDEN_CUBES',flush=True)
    ordinary=fmpq_mat([r[:-1] for r in integer_rows]).rank();augmented=fmpq_mat(integer_rows).rank()
    record=dict(status='EXACT_HEAD_EXCHANGE_REPAIR_EXISTS' if ordinary==augmented else 'EXACT_HEAD_EXCHANGE_REPAIR_OBSTRUCTION',
                ranks=[ordinary,augmented],witnesses=witnesses,segments=segments,forbidden_cubes=bad,integer_rows=integer_rows,
                baseline=[dict(head=h,edges=es,coefficient=str(c)) for (h,es),c in sorted(baseline.items())])
    if ordinary==augmented:
        rr,rank=fmpq_mat(integer_rows).rref();coefficients=[Q(0)]*len(relations)
        for i in range(rank):
            p=next(j for j in range(len(relations)) if rr[i,j]);coefficients[p]=Q(str(rr[i,len(relations)]))
        chain=defaultdict(Q,baseline)
        for coefficient,relation in zip(coefficients,relations):
            for key,v in relation.items():chain[key]+=coefficient*v
        chain={k:v for k,v in chain.items() if v}
        assert not boundary(chain) and all(is_nc(k) for k in chain)
        record['exchange_coefficients']=list(map(str,coefficients))
        record['chain']=[dict(head=h,edges=es,coefficient=str(c)) for (h,es),c in sorted(chain.items())]
        record['chain_support']=len(chain);record['exchange_support']=sum(bool(c) for c in coefficients)
    record.update(producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started,
                  scope='First four-simplex boundary lift, corrected only by single-edge-head exchange relations on four-label trees. This is not a uniform upper theorem.')
    (HERE/'overnight_upper_ordered_exchange.json').write_text(json.dumps(record,indent=2)+'\n')
    print(record['status'],record['ranks'],'SUPPORT',record.get('chain_support'),'SECONDS',record['seconds'],flush=True)


if __name__=='__main__':main()
