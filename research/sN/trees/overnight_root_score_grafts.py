#!/usr/bin/env python3
"""Additional exact necessary gates for the unproved Q_* score.

The source relations are fixed-apex S4 rational evaluation relations, as in
the frozen generator gate.  A violation needs a symbolic source identity
check before it becomes a refutation.  Passing does not prove descent.
"""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import time
from flint import fmpq, fmpq_mat
from overnight_uniform_pruning_candidate_target import score

HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic()
    data=json.loads((HERE/'overnight_uniform_pruning_generator_gate_rows.json').read_text())
    units=data['units']; matrix=fmpq_mat([[fmpq(s) for s in row] for row in data['rows']])
    rr,rank=matrix.rref(); n=len(units)
    piv=[next(j for j in range(n) if rr[i,j]) for i in range(rank)]
    null=[]
    for j in range(n):
        if j in piv:continue
        vec=[Q(0)]*n;vec[j]=Q(1)
        for i,k in enumerate(piv):vec[k]=-Q(str(rr[i,j]))
        null.append(vec)
    results=[]
    for kind in ('internal_path','same_two_arms','distinct_two_arms'):
        for signs in product((-1,1),repeat=4):
            values=[]
            for unit in units:
                total=Q(0)
                for v in range(1,5):
                    choices=range(1,5) if kind=='distinct_two_arms' else (v,)
                    for w in choices:
                        if kind=='distinct_two_arms' and v==w:continue
                        if kind=='internal_path': extra=[(v,6),(5,6),(6,7),(7,8)]
                        else: extra=[(v,5),(5,6),(w,7),(7,8)]
                        oriented=[(b,a) if s==1 else(a,b) for (a,b),s in zip(extra,signs)]
                        total+=score({'root':unit['root'],'edges':[tuple(e) for e in unit['edges']]+oriented})
                values.append(total)
            bad=[]
            for vec in null:
                pairing=sum(v*c for v,c in zip(values,vec))
                if pairing:bad.append((sum(bool(x) for x in vec),vec,pairing))
            row=dict(kind=kind,signs=signs,score_sum=list(map(str,values)),violated=len(bad))
            if bad:
                _,vec,pairing=min(bad,key=lambda x:x[0]);row.update(relation=list(map(str,vec)),pairing=str(pairing))
            results.append(row)
    report=dict(status='NECESSARY_GATE_VIOLATION' if any(r['violated'] for r in results) else 'NECESSARY_GATES_PASS',
                source_rank=rank,source_columns=n,source_relations=len(null),gates=results,
                seconds=round(time.monotonic()-start,3),
                scope='Finite necessary tests only; neither quotient descent nor an all-tree lower bound is proved.')
    (HERE/'overnight_root_score_grafts.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='gates'}),flush=True)
    for r in results:
        if r['violated']:print(json.dumps(r),flush=True)


if __name__=='__main__':main()
