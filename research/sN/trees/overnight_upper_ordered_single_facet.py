#!/usr/bin/env python3
"""Actual undoubled simplex lifts: only the root-omitting coface fills.

The assertion is checked on every coface of three actual corrected lifts,
not on an auxiliary graph model.
"""
from collections import defaultdict
from pathlib import Path
import hashlib,json,time
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_undoubled as undoubled
import overnight_upper_triangle_attachments as attachment
import overnight_upper_product_family as base

HERE=Path(__file__).parent

def coface(chain,n,missing):
    injection=[i for i in range(n+1) if i!=missing]
    def image(vector):
        out=[0]*(n+1)
        for i,x in enumerate(vector):out[injection[i]]=x
        return tuple(out)
    result=defaultdict(int)
    for (head,edges),c in chain.items():
        item=base.normalize_cube(image(head),[image(e) for e in edges],c)
        if item:result[item[0]]+=item[1]
    return coherent.clean(result)

def main():
    start=time.monotonic();records=[]
    triangle=attachment.raw_chain(3,(((0,1,2),0,1),))
    X,_=contraction.contract(coherent.delta({k:-v for k,v in triangle.items()},3),4)
    for dimension in (3,4,5):
        n=dimension+1
        fixed,boundary,correction=undoubled.correction(X,n)
        hx,_=contraction.contract(X,n)
        hf,_=contraction.contract(fixed,n)
        assert not hx and not hf,'both filled and canonically corrected lifts are in ker H'
        exceptional,exceptional_stats=contraction.contract(coface(fixed,n,0),n+1)
        vanish=[]
        for missing in range(1,n+1):
            value,_=contraction.contract(coface(fixed,n,missing),n+1)
            assert not value,('root-preserving coface',dimension,missing)
            vanish.append(missing)
        full,full_stats=contraction.contract(boundary,n+1)
        assert exceptional==full,'all alternating cofaces reduce to the exceptional one'
        assert coherent.boundary(exceptional)==boundary,'actual next simplex lift'
        record=dict(simplex_dimension=dimension,input_cubes=len(X),
                    corrected_cubes=len(fixed),full_boundary_cubes=len(boundary),
                    exceptional_coface_cubes=len(coface(fixed,n,0)),
                    output_cubes=len(exceptional),individually_zero_cofaces=vanish,
                    exceptional_contraction=exceptional_stats,full_contraction=full_stats)
        records.append(record)
        print('ACTUAL SINGLE COFACE',dimension,'INPUT',len(fixed),'OUTPUT',len(full),
              'SECONDS',time.monotonic()-start,flush=True)
        X=exceptional
    result=dict(status='EXACT_ACTUAL_ORDERED_SIMPLEX_SINGLE_COFACE_CONTROLS',
                records=records,seconds=time.monotonic()-start,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='The single-coface identity has a uniform contraction-naturality proof; these are exact controls on actual simplex lifts. The remaining support growth of head expansion and closed augmentation corrections is not bounded exponentially.')
    (HERE/'overnight_upper_ordered_single_facet.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
