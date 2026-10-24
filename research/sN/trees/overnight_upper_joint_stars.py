#!/usr/bin/env python3
"""Joint ordinary/midpoint general-head families; separate failures do not add."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import random
import sys
import time

from flint import fmpq_mat
import overnight_upper_star_heads as S
import overnight_upper_midpoint as M
from rational_identity import add,Verifier
from overnight_upper_probe import digest

HERE=Path(__file__).parent


def main(n):
    started=time.monotonic();hs=S.histograms(n-2,len(M.H));hm=S.histograms(n-3,len(M.H))
    width=len(hs)+len(M.D)*len(hm);rng=random.Random(24102483+n);rows=[];points=[]
    while len(points)<width+10:
        p=[rng.randrange(1,120) for _ in range(n-1)];p.append(-sum(p))
        try:row=S.values(p,M.H,hs)[:-1]+M.values(p,hm)
        except ZeroDivisionError:continue
        rows.append(row);points.append(p)
    rr,rank=fmpq_mat([[str(q) for q in r] for r in rows]).rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)];target=width in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,head_values=list(map(str,M.H)),core_parameters=list(map(str,M.D)),
              star_columns=len(hs),midpoint_columns=len(M.D)*len(hm),points=points,
              rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target),rank],
              producer_sha256=digest(Path(__file__)),star_source_sha256=digest(Path(S.__file__)),
              midpoint_source_sha256=digest(Path(M.__file__)))
    print('EXACT RANKS',data['ranks'],'COLS',width,'SECONDS',time.monotonic()-started,flush=True)
    stars=S.family(n,M.H,hs);mids=M.units(n,hm)
    def expr(cs,with_target):
        out=S.exact_expression(n,stars,cs[:len(hs)])
        for key,c in M.expression(n,mids,cs[len(hs):],False).items():out[key]+=c
        if not with_target:
            fs,aa,den=M.affine_forms(n,mids[0][0])
            add(out,(-1)**(n-1),(0,)*(n-1)+(1,),0,[(f,1) for f in fs])
        return out
    V=Verifier(budget=180)
    if target:
        free=[j for j in range(width) if j not in pivots];vectors=[]
        for f in free:
            cs=[Q(0)]*width;cs[f]=1
            for i,j in enumerate(pivots):
                if j<width:cs[j]=-Q(str(rr[i,f]))
            assert V.check(expr(cs,False))
            vectors.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='EXACT_JOINT_STAR_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=vectors,
                    exact_kernel_count=len(vectors),ordinary_rank_upper=width-len(vectors))
    else:
        cs=[Q(0)]*width
        for i,j in enumerate(pivots):cs[j]=Q(str(rr[i,width]))
        assert V.check(expr(cs,True))
        data.update(status='EXACT_TOP_IDENTITY',coefficients=list(map(str,cs)))
    data.update(symbolic_calls=V.calls,elapsed_seconds=time.monotonic()-started)
    label='reciprocal_' if Q(-1,2) in M.H else ''
    (HERE/f'overnight_upper_joint_stars_{label}{n}.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':
    if len(sys.argv)>2 and sys.argv[2]=='reciprocal':M.H=(-2,-1,Q(-1,2),0,1)
    main(int(sys.argv[1]))
