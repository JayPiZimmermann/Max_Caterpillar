#!/usr/bin/env python3
"""Close the two-core family under deletion by adjoining full single cores."""
from fractions import Fraction as Q
from pathlib import Path
import json
import random
import sys
import time

from flint import fmpq_mat
import overnight_upper_two_circuits as T
import overnight_upper_circuit as C
from overnight_upper_probe import digest
from rational_identity import Verifier

HERE=Path(__file__).parent


def main(n):
    started=time.monotonic();keys,two=T.family(n);unused,ck,cols=C.family(n,3)
    extra=[col for key,col in zip(ck,cols) if key[0]==n-1];width=len(two)+len(extra)
    print('FAMILY',n,'TWO',len(two),'EXTRA',len(extra),flush=True)
    rng=random.Random(24102497+n);rows=[];points=[]
    while len(rows)<width+10:
        p=[rng.randrange(1,1000) for _ in range(n-1)];p.append(-sum(p))
        try:row=T.values(n,two,p)[:-1]+C.values(n,extra,p)
        except ZeroDivisionError:continue
        rows.append(row);points.append(p)
        if len(rows)%20==0:print('ROWS',len(rows),'SECONDS',time.monotonic()-started,flush=True)
    rr,rank=fmpq_mat([[str(q) for q in r] for r in rows]).rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,two_core_columns=len(two),full_single_core_columns=len(extra),
              points=points,rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target),rank],
              producer_sha256=digest(Path(__file__)),two_core_source_sha256=digest(Path(T.__file__)),
              single_core_source_sha256=digest(Path(C.__file__)))
    print('EXACT RANKS',data['ranks'],'SECONDS',time.monotonic()-started,flush=True)
    independent=[sum((T.coordinate_value(n,u,points[0]) for u in col),Q(0)) for col in two]
    independent.extend(sum((C.coordinate_value(n,u,points[0]) for u in col),Q(0)) for col in extra)
    assert independent==rows[0][:-1];data['independent_coordinate_full_rows']=1
    path=HERE/f'overnight_upper_two_circuits_union_{n}.json';path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    def expr(cs,target):
        out=T.expression(n,two,cs[:len(two)],target)
        for term,c in C.expression(n,extra,cs[len(two):],False).items():out[term]+=c
        return out
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            assert V.check(expr(cs,False));vectors.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='EXACT_TWO_CIRCUIT_UNION_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=vectors,
                    exact_kernel_count=len(vectors),ordinary_rank_upper=width-len(vectors))
    else:
        cs=[Q(0)]*width
        for i,j in enumerate(pivots):cs[j]=Q(str(rr[i,width]))
        data['coefficients']=list(map(str,cs));path.write_text(json.dumps(data,separators=(',',':'))+'\n')
        assert V.check(expr(cs,True));data['status']='EXACT_TOP_IDENTITY'
    data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]))
