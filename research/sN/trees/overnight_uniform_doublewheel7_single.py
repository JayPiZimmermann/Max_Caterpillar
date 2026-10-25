#!/usr/bin/env python3
"""Locate the remaining poles of the exact two-term N7 witness."""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib,json,math,time
from overnight_uniform_doublewheel7_verify import UNITS,WEIGHTS,positive_sides,add
from overnight_uniform_doublewheel7_branches import primitive,evaluate


def chart(kind,k):
    standard=lambda i:tuple(int(j==i)for j in range(6))
    frequency=[];next_coordinate=0
    if kind=='cut':
        total=standard(5)
        for _ in range(k-1):
            vector=standard(next_coordinate);next_coordinate+=1
            frequency.append(vector);total=tuple(x-y for x,y in zip(total,vector))
        frequency.append(total)
    else:
        assert kind=='minus'
        frequency=[standard(0)];next_coordinate=1
        total=tuple(x-y for x,y in zip(standard(0),standard(5)))
        for _ in range(k-1):
            vector=standard(next_coordinate);next_coordinate+=1
            frequency.append(vector);total=tuple(x-y for x,y in zip(total,vector))
        frequency.append(total)
    while len(frequency)<6:
        frequency.append(standard(next_coordinate));next_coordinate+=1
    frequency.append(tuple(-sum(v[j]for v in frequency)for j in range(6)))
    assert next_coordinate==5 and all(sum(v[j]for v in frequency)==0 for j in range(6))
    return frequency


def residues(root,edges,frequency):
    sides=positive_sides(root,edges);result=Counter()
    for perm in permutations(range(7)):
        apex=frequency[perm[0]];numerator,scale=primitive(apex[:5])
        forms=[]
        for side,head in sides:
            q=apex if head else (0,)*6
            for v in side:q=add(q,frequency[perm[v]])
            forms.extend((q,add(q,apex)))
        zero=[v for v in forms if not any(v[:5])]
        assert len(zero)<=1
        if not zero:continue
        den=[];common=zero[0][5]
        for f in forms:
            if not any(f[:5]):continue
            p,d=primitive(f[:5]);den.append(p);common*=d
        result[(numerator,tuple(sorted(den)))]+=Q((-scale)**3,common)
    return {key:c for key,c in result.items()if c}


def main():
    started=time.monotonic();rows=[];point=(1,10,100,1000,10000)
    for kind,k in [('cut',2),('cut',3)]+[('minus',k)for k in range(1,6)]:
        frequency=chart(kind,k)
        tables=[residues(root,edges,frequency)for root,edges in UNITS]
        combined=Counter()
        for w,table in zip(WEIGHTS,tables):
            for key,c in table.items():combined[key]+=w*c
        combined={key:c for key,c in combined.items()if c}
        individual=[evaluate(table,point)for table in tables]
        value=sum(w*v for w,v in zip(WEIGHTS,individual))
        assert evaluate(combined,point)==value
        rows.append(dict(kind=kind,size=k,symbolic_fraction_dictionary_zero=not combined,
                         surviving_fraction_records=len(combined),individual_values=list(map(str,individual)),witness_value=str(value)))
        print(json.dumps(rows[-1]),flush=True)
    data=dict(status='EXACT_SINGLE_POLE_CONTROLS_ON_N7_OUTWARD_TWIN_WITNESS',rows=rows,
              free_frequency_point=point,seconds=time.monotonic()-started,
              producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Dictionary cancellation proves exact zero residue. A nonzero rational evaluation proves a genuine pole. A zero evaluation with surviving records is inconclusive.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
