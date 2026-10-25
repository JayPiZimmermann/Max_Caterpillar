#!/usr/bin/env python3
"""Baxter-local swap attachment state, with its complete top face family."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,random,sys,time
from flint import nmod_mat
import overnight_upper_baxter_union as probe
from overnight_upper_baxter_union_exact import expression,unit
HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import Verifier

def main():
    start=time.monotonic();basepath=HERE/'overnight_upper_baxter_union.json'
    base=json.loads(basepath.read_text());n=base['labels'];words=base['class_words']
    changed=[a for a,b in zip(words[0],words[1]) if a!=b];assert len(changed)==2
    v,w=changed;sources=set()
    for data in base['sources']:
        head,edges=unit(data)
        for shift in (-1,0,1):
            h=list(head);h[v]+=shift;h[w]-=shift;sources.add((tuple(h),edges))
    sources=sorted(sources);forms=[probe.factors(n,u) for u in sources]
    target=[(probe.factors(n,unit(u)),c) for u,c in base['target']]
    rng=random.Random(25102548);rows=[];points=[];p=probe.PRIME
    while len(rows)<len(sources)+12:
        values=[rng.randrange(1,30000) for _ in range(n-1)];point=[-sum(values)]+values
        try:
            row=[probe.value(n,f,point,p) for f in forms]
            rhs=sum(c*probe.value(n,f,point,p) for f,c in target)%p
        except ZeroDivisionError:continue
        points.append(point);rows.append(row+[rhs])
    rr,rank=nmod_mat(rows,p).rref()
    pivots=[next(j for j in range(len(sources)+1) if rr[i,j]) for i in range(rank)]
    gap=len(sources) in pivots
    result=dict(status='MODULAR_BAXTER_SWAP_HEAD_GAP' if gap else 'MODULAR_BAXTER_SWAP_HEAD_INCLUSION',
        source_certificate_sha256=hashlib.sha256(basepath.read_bytes()).hexdigest(),
        class_words=words,swap_labels=changed,source_columns=len(sources),sources=sources,
        ranks=[rank-int(gap),rank],points=points,prime=p,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Only the local incomparable-label head shift is added; all its cycle top faces are included. No arbitrary head alphabet and no uniform construction assertion.')
    if not gap:
        proposal=[Q(0)]*len(sources)
        for i,j in enumerate(pivots):proposal[j]=probe.reconstruct(int(rr[i,len(sources)]),p)
        if all(c is not None for c in proposal):
            residual=defaultdict(Q)
            for u,c in zip(sources,proposal):
                if c:
                    key,a=expression(n,u);residual[key]+=c*a
            for data,c in base['target']:
                key,a=expression(n,unit(data));residual[key]-=c*a
            verifier=Verifier(budget=120)
            if verifier.check(dict(residual)):
                result.update(status='EXACT_BAXTER_SWAP_HEAD_CLASS_IDENTITY',
                              coefficients=[[i,str(c)] for i,c in enumerate(proposal) if c],
                              principal_part_calls=verifier.calls)
            else:result['status']='BAXTER_SWAP_HEAD_RECONSTRUCTION_FAILED'
        else:result['status']='BAXTER_SWAP_HEAD_RECONSTRUCTION_HEIGHT_STOP'
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_baxter_swap_head.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'COLUMNS',len(sources),'RANKS',result['ranks'],
          'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
