#!/usr/bin/env python3
"""Full S6 necessary control for every two-component forest product shape."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib,json,random,time
from flint import nmod_mat
import overnight_upper_product_family as base

HERE=Path(__file__).parent


def main():
    start=time.monotonic();n=6
    descriptors=[(0,(1,),((2,3),(2,4),(2,5))),
                 (0,(1,),((2,3),(3,4),(4,5))),
                 (0,(1,2),((1,2),(3,4),(4,5)))]
    base.group=lambda arity:list(permutations(range(arity)))
    columns=[base.expression(base.sym_chain(n,d)) for d in descriptors];wanted=base.target(n)
    planes=sorted(set(wanted)|{p for e in columns for p in e});points=[];rows=[];rng=random.Random(251028)
    print('INVENTORY',len(columns),'S6 SHAPE COLUMNS',len(planes),'SPAN PLANES','SECONDS',time.monotonic()-start,flush=True)
    for plane in planes:
        accepted=0
        while accepted<3:
            point=tuple(rng.randrange(1,1000) for _ in range(n-2))
            try:row=[base.evaluate(e.get(plane,{}),point) for e in columns]+[base.evaluate(wanted.get(plane,{}),point)]
            except ZeroDivisionError:continue
            rows.append(row);points.append((plane,point));accepted+=1
    rr,rank=nmod_mat(rows,base.PRIME).rref();pivots=[next(j for j in range(4) if rr[i,j]) for i in range(rank)]
    ranks=[rank-int(3 in pivots),rank]
    result=dict(status='MODULAR_FULL_SYMMETRIC_PRODUCT_DIAGNOSTIC',n=n,descriptors=descriptors,permutations=720,
                planes=planes,points=points,prime=base.PRIME,modular_rows=rows,ranks=ranks,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                kernel_producer_sha256=hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
                scope='All two-component forest triangle products on six labels, up to global reflection exchanging the component signs; no noncrossing restriction.')
    if rank==4:result['status']='EXACT_FULL_SYMMETRIC_PRODUCT_OBSTRUCTION'
    elif 3 in pivots:
        ordinary=[p for p in pivots if p<3];free=[j for j in range(3) if j not in ordinary]
        verifier=base.Verifier(240);relations=[]
        for j in free:
            coeff=[Q(0)]*3;coeff[j]=Q(1)
            for i,p in enumerate(pivots):
                if p<3:coeff[p]=-base.ratrec(int(rr[i,j]),base.PRIME)
            for plane in planes:
                expression=defaultdict(Q)
                for c,col in zip(coeff,columns):
                    for key,v in col.get(plane,{}).items():expression[key]+=c*v
                assert verifier.check(expression),('failed exact shape relation',j,plane)
            relations.append(list(map(str,coeff)))
        result['exact_relations']=relations;result['status']='EXACT_FULL_SYMMETRIC_PRODUCT_OBSTRUCTION'
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_product_symmetric_6.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('DONE',result['status'],'RANKS',ranks,'SECONDS',result['seconds'],flush=True)


if __name__=='__main__':main()
