#!/usr/bin/env python3
"""Exact first recursive pole controls on one endpoint relation residue.

Exploit the proved S_k x S_(9-k) symmetry to choose one representative
of each remaining pole orbit. Nonempty children remain unresolved.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import gzip,hashlib,json,math,time

HERE=Path(__file__).parent


def orbit_key(form,k):
    blocks=[list(form[:k-1])+[0],list(form[k-1:])+[0]]
    options=[]
    for sign in(1,-1):
        values=[]
        for block in blocks:
            b=sorted(sign*x for x in block);values.append(tuple(x-b[0]for x in b))
        divisor=math.gcd(*(x for b in values for x in b))
        options.append(tuple(tuple(x//divisor for x in b)for b in values))
    return min(options)


def normalize(form):
    g=math.gcd(*form)
    assert g
    if next(x for x in form if x)<0:g=-g
    return tuple(x//g for x in form),g


def restrict(form,alpha,pivot):
    raw=tuple(alpha[pivot]*form[j]-form[pivot]*alpha[j]for j in range(len(form))if j!=pivot)
    if not any(raw):return None,Q(0)
    primitive,g=normalize(raw)
    return primitive,Q(g,alpha[pivot])


def main(k=4):
    started=time.monotonic();file=HERE/f'overnight_uniform_endpoint_q2_residue_{k}.fractions.json.gz'
    data=json.load(gzip.open(file,'rt'));forms=[tuple(f)for f in data['linear_forms']];records=data['records']
    uses=Counter(j for record in records for j in record['denominator']);orbits={}
    for j in uses:orbits.setdefault(orbit_key(forms[j],k),[]).append(j)
    rows=[];children=[]
    for key,indices in sorted(orbits.items()):
        index=min(indices,key=lambda j:(uses[j],j));alpha=forms[index];pivot=next(i for i,x in enumerate(alpha)if x)
        reduced={};total=Counter()
        for record in records:
            denominator=record['denominator']
            if index not in denominator:continue
            assert denominator.count(index)==1
            numerator,numerator_scale=restrict(forms[record['numerator']],alpha,pivot)
            if numerator is None:continue
            coefficient=Q(record['coefficient'])*numerator_scale**4
            factors=[]
            for j in denominator:
                if j==index:continue
                if j not in reduced:reduced[j]=restrict(forms[j],alpha,pivot)
                f,scale=reduced[j];assert f is not None
                factors.append(f);coefficient/=scale
            total[(numerator,tuple(sorted(factors)))]+=coefficient
        total={key:c for key,c in total.items()if c}
        multiplicity=max((max(Counter(den).values())for num,den in total),default=0)
        row=dict(orbit_key=key,orbit_size=len(indices),representative=alpha,selected_records=uses[index],
                 surviving_records=len(total),dictionary_cancels=not total,largest_pole_multiplicity=multiplicity)
        rows.append(row)
        if total:children.append(dict(representative=alpha,normal_coordinate_pivot=pivot,
                                      records=[dict(numerator=num,denominator=den,coefficient=str(c))for(num,den),c in total.items()]))
        print(json.dumps(row),flush=True)
    output=dict(status='EXACT_RECURSIVE_POLE_ORBIT_CONTROLS_ENDPOINT_Q2',subset_size=k,orbits=len(orbits),rows=rows,
                all_children_cancel=not children,seconds=time.monotonic()-started,
                input_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='All first remaining ambient poles are simple. Symmetry reduces their vanishing tests to the listed orbits. Nonempty child dictionaries do not refute zero; higher pole multiplicities must be retained in further recursion.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(output,indent=2)+'\n')
    with gzip.open(str(Path(__file__).with_suffix(''))+'.children.json.gz','wt')as f:json.dump(children,f,separators=(',',':'))
    print('seconds',output['seconds'],'unresolved children',len(children),flush=True)


if __name__=='__main__':main()
