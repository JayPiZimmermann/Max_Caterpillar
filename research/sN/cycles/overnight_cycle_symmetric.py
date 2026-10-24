#!/usr/bin/env python3
"""All labelings of canonical cycles and every top-dimensional face state.

This larger full-permutation family is not exponentially sized. It is a
structural control for possible cyclic constructions and exclusions.
"""
from pathlib import Path
import hashlib,itertools,json,sys,time
import overnight_cycle_affine as A
from cycle_fourier import family,permute

HERE=Path(__file__).resolve().parent


def stem(n):return HERE/f'overnight_cycle_symmetric_{n}'


def shape_orders(key):
    h,edges=key;n=len(h);vertices={v for e in edges for v in e};apex,=set(range(n))-vertices
    adjacency={v:[] for v in vertices}
    for u,v in edges:adjacency[u].append(v);adjacency[v].append(u)
    endpoints=[v for v in vertices if len(adjacency[v])==1]
    assert len(endpoints) in (0,2)
    for start in endpoints or sorted(vertices):
        for first in adjacency[start]:
            order=[start,first]
            while len(order)<len(vertices):
                nxt=[v for v in adjacency[order[-1]] if v!=order[-2] and v not in order]
                assert len(nxt)==1
                order.append(nxt[0])
            pi=[0]*n;pi[apex]=0
            for j,v in enumerate(order):pi[v]=j+1
            yield tuple(pi)


def inventory(n):
    started=time.monotonic();base=family(n);reps={}
    for key,(apex,atoms) in base.items():
        images=[(permute(key,pi),pi) for pi in shape_orders(key)]
        representative,pi=min(images)
        reps.setdefault(representative,tuple(permute(atom,pi) for atom in atoms))
    result=dict(status='EXACT_COLORED_CYCLE_PATH_INVENTORY',n=n,base_units=len(base),
                representatives=[[k,reps[k]] for k in sorted(reps)],orbit_count=len(reps),
                producer_sha256=A.sha(Path(__file__)),cycle_source_sha256=A.sha(HERE/'cycle_fourier.py'),
                seconds=time.monotonic()-started)
    stem(n).with_suffix('.inventory.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='representatives'}),flush=True)


def expand(n):
    started=time.monotonic();inv=json.loads(stem(n).with_suffix('.inventory.json').read_text());columns=[];units=[]
    perms=list(itertools.permutations(range(n)))
    for (h,es),raw_atoms in inv['representatives']:
        key=tuple(h),tuple(map(tuple,es));atoms=[(tuple(hh),tuple(map(tuple,ee))) for hh,ee in raw_atoms]
        images={}
        for pi in perms:
            unit=permute(key,pi)
            if unit not in images:images[unit]=tuple(permute(atom,pi) for atom in atoms)
        units.append(sorted(images));columns.append([atom for unit in sorted(images) for atom in images[unit]])
    result=dict(status='EXACT_FAMILY_ENUMERATION_NO_SPAN_CLAIM',n=n,group_order=len(perms),
                base_units=inv['base_units'],orbit_count=len(columns),unit_count=sum(map(len,units)),
                atom_occurrences=sum(map(len,columns)),units=units,columns=columns,
                producer_sha256=A.sha(Path(__file__)),inventory_sha256=A.sha(stem(n).with_suffix('.inventory.json')),
                seconds=time.monotonic()-started)
    stem(n).with_suffix('.family.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('units','columns')}),flush=True)


if __name__=='__main__':
    mode,n=sys.argv[1],int(sys.argv[2]);A.stem=stem
    if mode in ('inventory','expand'):globals()[mode](n)
    else:getattr(A,mode)(n)
