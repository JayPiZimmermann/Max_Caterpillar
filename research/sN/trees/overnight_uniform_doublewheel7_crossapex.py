#!/usr/bin/env python3
"""Exact cross-apex shifted-cut control on the N7 witness."""
from collections import Counter
from pathlib import Path
import hashlib,json,time
from overnight_uniform_doublewheel7_verify import UNITS,WEIGHTS
from overnight_uniform_doublewheel7_branches import residue_tables,evaluate


def chart(size):
    # H1=omega0-sum_S=s, H2=omega_b-sum_S=t.
    e=lambda j:tuple(int(i==j)for i in range(6))
    plus=lambda *vectors:tuple(sum(v[i]for v in vectors)for i in range(6))
    negative=lambda v:tuple(-x for x in v)
    frequency=[e(0)];j=1;remaining=plus(e(0),negative(e(4)))
    for _ in range(size-1):
        frequency.append(e(j));remaining=plus(remaining,negative(e(j)));j+=1
    frequency.append(remaining)
    frequency.append(plus(e(0),negative(e(4)),e(5)))
    while len(frequency)<6:frequency.append(e(j));j+=1
    frequency.append(negative(plus(*frequency)))
    assert j==4 and len(frequency)==7
    return frequency


def main():
    started=time.monotonic();rows=[];point=(1,10,100,1000)
    for size in(3,4):
        frequency=chart(size)
        tables=[residue_tables(root,edges,frequency)for root,edges in UNITS]
        for order in(0,1):
            combined=Counter()
            for w,ts in zip(WEIGHTS,tables):
                for key,c in ts[order].items():combined[key]+=w*c
            combined={key:c for key,c in combined.items()if c}
            values=[evaluate(ts[order],point)for ts in tables]
            value=sum(w*v for w,v in zip(WEIGHTS,values))
            assert value==evaluate(combined,point)
            row=dict(subset_size=size,order='s_then_t'if order==0 else't_then_s',
                     symbolic_fraction_dictionary_zero=not combined,surviving_fraction_records=len(combined),
                     individual_values=list(map(str,values)),witness_value=str(value))
            rows.append(row);print(json.dumps(row),flush=True)
    data=dict(status='EXACT_CROSS_APEX_CUT_POLE_CONTROL',rows=rows,free_frequency_point=point,
              frequency_rule='H1=omega_a-sum_S=s; H2=omega_b-sum_S=t, a,b outside S',
              seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='A nonzero value detects this witness only; no injectivity or separator claim.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
