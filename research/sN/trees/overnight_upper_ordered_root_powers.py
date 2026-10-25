#!/usr/bin/env python3
"""Bounded exact powers of A=H phi_0, without changing prior artifacts."""
from pathlib import Path
import hashlib,json,time
import overnight_upper_ordered_coherent as coherent
import overnight_upper_ordered_contraction as contraction
import overnight_upper_ordered_single_facet as single
import overnight_upper_ordered_root_transfer as transfer
import overnight_upper_triangle_attachments as attachment
import overnight_upper_product_family as base

HERE=Path(__file__).parent

def main():
    start=time.monotonic();records=[]
    seeds=[
        ('actual_X3',4,coherent.multiply(transfer.edge(4,1,0),
          attachment.raw_chain(4,(((1,2,3),1,1),)))),
        ('constant_z21',3,transfer.z(3,2,1)),
        ('constant_two_z',4,coherent.multiply(transfer.z(4,2,1),transfer.z(4,3,2))),
    ]
    for name,n,seed in seeds:
        X=seed;track=[]
        for power in range(1,6):
            if len(X)>30000:break
            X,stats=contraction.contract(single.coface(X,n,0),n+1);n+=1
            abstract=contraction.expand_basis(contraction.to_abstract(X,n),n,True)
            first_stars=sorted({min((i for kind,i,j in edges if kind==0),default=-1)
                               for (head,edges),c in abstract.items()})
            record=dict(power=power,labels=n,cubes=len(X),abstract_terms=len(abstract),
                        first_star_positions=first_stars,
                        max_head_l1=max((sum(abs(v) for v in h[1:]) for h,e in X),default=0))
            track.append(record)
            print('ROOT POWER',name,record,'SECONDS',time.monotonic()-start,flush=True)
            if not X:break
        records.append(dict(seed=name,records=track))
    result=dict(status='BOUNDED_EXACT_ROOT_TRANSFER_POWER_CONTROLS',records=records,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-start,
                scope='Raw operator powers, not corrected simplex lifts; no growth theorem inferred.')
    (HERE/'overnight_upper_ordered_root_powers.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
