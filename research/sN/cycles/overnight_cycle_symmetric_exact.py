#!/usr/bin/env python3
"""Exact right-kernel gate for the complete endpoint-shifted path family.

Full cycles tile into this path family. Twelve independent rational identities
bound its rank by126; a separate scalar modular elimination checks augmented
rank127. Symmetric principal-part checks prove identities, not sampled zeros.
"""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib,itertools,json,math,sys,time
import numpy as np
import overnight_cycle_affine as A
from overnight_cycle_symmetric import shape_orders
from cycle_fourier import cuts,permute
from rational_identity import Verifier,add
from overnight_upper_modular_residues import invariance,principal_parts

HERE=Path(__file__).resolve().parent
BASE=HERE/'overnight_cycle_symmetric_7'
OUTPUT=BASE.with_suffix('.exact.json')
N=7;P=1000000007


def scalar_rank(rows):
    basis={};selected=[]
    for i,row in enumerate(rows):
        v=list(map(int,row))
        for j,b in sorted(basis.items()):
            a=v[j]
            if a:
                for k in range(j,len(v)):v[k]=(v[k]-a*b[k])%P
        nz=next((j for j,x in enumerate(v) if x),None)
        if nz is not None:
            inv=pow(v[nz],-1,P);basis[nz]=[x*inv%P for x in v];selected.append(i)
    return len(basis),selected


def expression(reps,vector):
    fs=[tuple(int(i==j) for i in range(N-1))+(0,) for j in range(N-1)]+[(-1,)*(N-1)+(0,)]
    out=defaultdict(Q)
    for index,coeff in vector:
        (h,edges),atoms=reps[index];key=tuple(h),tuple(map(tuple,edges));assert len(edges)==N-2
        automorphisms=sum(permute(key,pi)==key for pi in shape_orders(key));assert automorphisms in (1,2)
        c=Q(coeff)/automorphisms
        for pi in itertools.permutations(range(N)):
            unit=permute(key,pi);apex=pi[0];den=[]
            for side,H in cuts(unit,apex):
                q=tuple(sum(fs[v][j] for v in side) for j in range(N))
                den.extend([(tuple(x+H*a for x,a in zip(q,fs[apex])),1),
                            (tuple(x+(H+1)*a for x,a in zip(q,fs[apex])),1)])
            add(out,c,tuple(-x for x in fs[apex]),N-4,den)
    return {k:c for k,c in out.items() if c}


def prove(expr,budget):
    assert all(k-sum(p for f,p in den)==-N for num,k,den in expr)
    generators=[[(i+1)%N for i in range(N)],[1,0]+list(range(2,N))]
    mappings=[invariance(expr,pi) for pi in generators]
    poles={f for num,k,den in expr for f,p in den};seen=set();representatives=[]
    for f in sorted(poles):
        if f in seen:continue
        orbit={f};todo=[f]
        while todo:
            g=todo.pop()
            for mapping in mappings:
                h=mapping[g][1];assert h in poles
                if h not in orbit:orbit.add(h);todo.append(h)
        seen.update(orbit);representatives.append((min(orbit),len(orbit)))
    assert seen==poles
    index={f:[] for f,size in representatives}
    for term,c in expr.items():
        for f,p in term[2]:
            if f in index:index[f].append((term,c))
    checker=Verifier(budget=budget)
    for f,size in representatives:
        for child in principal_parts(index[f],f).values():assert checker.check(child)
    return dict(terms=len(expr),poles=len(poles),pole_orbits=len(representatives),symbolic_calls=checker.calls)


def main():
    start=time.monotonic();inventory=json.loads(BASE.with_suffix('.inventory.json').read_text())
    proposals=json.loads(BASE.with_suffix('.path_kernels.json').read_text());reps=inventory['representatives']
    ids=proposals['path_columns'];free=proposals['kernel_free_columns'];vectors=proposals['kernel_vectors']
    assert ids==[j for j,(key,atoms) in enumerate(reps) if len(key[1])==N-2]
    assert len(ids)==138 and len(free)==len(vectors)==12
    for f,vector in zip(free,vectors):
        v={j:Q(c) for j,c in vector}
        assert len(v)==len(vector) and v[f]==1 and set(v)<=set(ids)
        assert all(v.get(g,Q(0))==0 for g in free if g!=f)
    raw=np.fromfile(BASE.with_suffix('.u32'),dtype=np.uint32).reshape(-1,len(reps)+1)
    pathrows=raw[:,ids+[len(reps)]]
    ordinary,_=scalar_rank(pathrows[:,:-1]);augmented,selected=scalar_rank(pathrows)
    assert [ordinary,augmented]==[126,127]
    names=[BASE.with_suffix('.inventory.json'),BASE.with_suffix('.path_kernels.json'),Path(__file__),
           HERE/'cycle_fourier.py',A.TREES/'overnight_upper_modular_residues.py',A.TREES/'all_tree_dfs/rational_identity.py']
    hashes={str(p.name):A.sha(p) for p in names}
    result=dict(status='EXACT_PATH_KERNEL_GATE_IN_PROGRESS',n=N,path_orbits=138,
                prime=P,independent_modular_ranks=[ordinary,augmented],independent_augmented_rows=selected,
                matrix_sha256=A.sha(BASE.with_suffix('.u32')),hashes=hashes,passed=[])
    if OUTPUT.exists():
        old=json.loads(OUTPUT.read_text());assert old['hashes']==hashes and old['matrix_sha256']==result['matrix_sha256']
        result['passed']=old['passed']
    done={x['index'] for x in result['passed']}
    OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
    for i,vector in enumerate(vectors):
        if i in done:continue
        if time.monotonic()-start>1000:break
        began=time.monotonic();expr=expression(reps,vector)
        print('ASSEMBLED',i,'TERMS',len(expr),'SECONDS',time.monotonic()-began,flush=True)
        try:receipt=prove(expr,max(1,1150-(time.monotonic()-start)))
        except TimeoutError:break
        receipt.update(index=i,seconds=time.monotonic()-began);result['passed'].append(receipt)
        OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
        print('KERNEL_PASS',i,'COMPLETE',len(result['passed']),'/',len(vectors),'SECONDS',time.monotonic()-start,flush=True)
    if len(result['passed'])==12:result['status']='EXACT_ENDPOINT_SHIFTED_PATH_OBSTRUCTION'
    else:result['status']='PARTIAL_EXACT_PATH_KERNEL_GATE'
    result['elapsed_this_run']=time.monotonic()-start
    OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],flush=True)


if __name__=='__main__':main()
