#!/usr/bin/env python3
"""Independently replay the full fixed-path max-substitution intersection.

The saved candidate catalogues are read, but all rational kernels are
reconstructed from inverse coordinate matrices. No producer cut formula
or modular rational reconstruction is reused.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json,time
from flint import nmod_mat
from overnight_upper_baxter_bridge_check import matrix_term
from overnight_upper_baxter_split_check import evaluate
from rational_identity import term,Verifier

HERE=Path(__file__).parent

def substitute(head,edges,a=3):
    key,c=matrix_term(4,head,edges)
    num,power,den=key
    def lift(f):
        return f[:-1]+(f[a-1] if a else 0,)+(f[-1],)
    out=defaultdict(Q)
    for v in (a,4):
        f=(-1,-1,-1,-1,0) if v==0 else tuple(int(i==v-1) for i in range(4))+(0,)
        k,d=term(-c,lift(num),power,[(lift(g),m) for g,m in den]+[(f,1)])
        out[k]+=d
    return dict(out)

def add_scaled(expr,other,c):
    for k,d in other.items():
        expr[k]+=c*d

def rank(columns,points,p):
    return nmod_mat([[sum(evaluate(k,c,point,p) for k,c in col.items())%p
                      for col in columns] for point in points],p).rank()

def canonical(head,edges):
    head=list(head);out=[]
    for u,v in edges:
        if u>v:
            head[u]+=1;head[v]-=1;u,v=v,u
        out.append((u,v))
    return tuple(head),tuple(sorted(out))

def main():
    start=time.monotonic()
    inputs=[HERE/'overnight_upper_baxter_vertex_split.json',
            HERE/'overnight_upper_correlated_head_closure.json',
            HERE/'overnight_upper_correlated_channels.json']
    base,closure,channels=[json.loads(p.read_text()) for p in inputs]
    record=next(r for r in base['records'] if r['split_label']==3)
    sources=[dict([matrix_term(5,row['head'],row['edges'])]) for row in record['sources']]
    p=base['prime'];points=closure['points'];kernels=[]
    for kernel in record['kernels']:
        expr=defaultdict(Q);vector=[0]*len(sources)
        for j,raw in kernel:
            c=Q(raw);add_scaled(expr,sources[j],c)
            vector[j]=c.numerator*pow(c.denominator,-1,p)%p
        assert Verifier(150).check(dict(expr));kernels.append(vector)
    assert nmod_mat(kernels,p).rank()==len(sources)-44
    assert rank(sources,points,p)==44
    H=((0,1),(1,2),(2,3));expected=set()
    for j,(u,v) in enumerate(H):
        for signs in product((-1,1),repeat=3):
            head=[0]*4;head[u]=signs[0];head[v]=-signs[0]
            edges=[edge if s==1 else edge[::-1]
                   for edge,s in zip(H[:j]+H[j+1:],signs[1:])]
            expected.add(canonical(head,edges))
    units=[(tuple(h),tuple(tuple(e) for e in edges)) for h,edges in closure['input_units']]
    assert set(units)==expected and len(units)==24
    targets=[substitute(h,e) for h,e in units]
    nulls=[]
    for kernel in closure['input_kernels']:
        expr=defaultdict(Q);vector=[0]*len(targets)
        for j,raw in kernel:
            c=Q(raw);add_scaled(expr,targets[j],c)
            vector[j]=c.numerator*pow(c.denominator,-1,p)%p
        assert Verifier(150).check(dict(expr));nulls.append(vector)
    assert nmod_mat(nulls,p).rank()==16
    assert rank(targets,points,p)==8
    assert rank(sources+targets,points,p)==48
    safe=[j for j,(h,e) in enumerate(units) if all(3 not in pair for pair in e)]
    assert {row['input_column'] for row in closure['safe_witnesses']}==set(safe)
    for row in closure['safe_witnesses']:
        expr=defaultdict(Q);add_scaled(expr,targets[row['input_column']],Q(-1))
        k,c=matrix_term(5,row['head'],row['edges']);expr[k]+=Q(row['coefficient'])*c
        assert Verifier(150).check(dict(expr))
        # A nonzero scalar multiple of a source is in the same span.
        assert c and any(len(src)==1 and k in src and src[k] for src in sources)
    assert rank([targets[j] for j in safe],points,p)==4
    orientation_targets=[]
    for signs in channels['orientations']:
        edges=[tuple(e) if s==1 else tuple(e[::-1])
               for e,s in zip(channels['old_edges'],signs)]
        orientation_targets.append(substitute(channels['old_head'],edges))
    assert rank(sources+orientation_targets,channels['points'],p)==48
    result=dict(status='INDEPENDENT_EXACT_FIXED_PATH_INTERSECTION_PASS',
        input_descriptions=24,input_rank=8,source_rank=44,joint_rank=48,
        intersection_rank=4,isolated_apex_rank=4,
        input_nulls=16,source_nulls=len(kernels),
        four_orientation_extension_rank=48,
        inputs=[dict(path=x.name,sha256=hashlib.sha256(x.read_bytes()).hexdigest()) for x in inputs],
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=time.monotonic()-start,
        scope='Finite top-kernel intersection only; no exclusion of graph-mixed sums or general exponential constructions.')
    (HERE/'overnight_root_correlated_verify.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
