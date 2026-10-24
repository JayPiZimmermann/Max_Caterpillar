#!/usr/bin/env python3
"""Exact small symmetric span tests for stars with noncanonical integer heads.

All rational evaluations are exact. Sampled rank alone is not promoted to a
characteristic-zero exclusion: the independent rational-function kernel gate
is required. No bounded family count is presented as a construction.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import random
import sys
import time

from flint import fmpq_mat
from exponential_families_probe import canonical,exact_expression
from rational_identity import Verifier,add
from cycle_fourier import chamber_value

HERE=Path(__file__).parent


def histograms(total,k):
    if k==1: return [(total,)]
    return [(j,)+t for j in range(total+1) for t in histograms(total-j,k-1)]


def values(point,H,hist):
    n=len(point);out={h:Q(0) for h in hist};zero=(0,)*len(H)
    for apex,a in enumerate(point):
        for centre in range(n):
            if centre==apex: continue
            dp={zero:Q(1)}
            for leaf,w in enumerate(point):
                if leaf in (apex,centre): continue
                factors=[Q(1,(w+h*a)*(w+(h+1)*a)) for h in H]
                nxt=defaultdict(Q)
                for counts,c in dp.items():
                    for i,f in enumerate(factors):
                        t=list(counts);t[i]+=1;nxt[tuple(t)]+=c*f
                dp=nxt
            for counts,c in dp.items():out[counts]+=(-a)**(n-4)*c
    return [out[h] for h in hist]+[Q((-1)**(n-1),math.prod(point))]


def family(n,H,hist):
    """Assignment-sum columns, with each distinct head assignment once."""
    columns={h:[] for h in hist}
    for apex in range(n):
        for centre in range(n):
            if apex==centre:continue
            leaves=[i for i in range(n) if i not in (apex,centre)]
            for digits in product(range(len(H)),repeat=n-2):
                h=[0]*n;h[apex]=-1
                for leaf,d in zip(leaves,digits):h[leaf]=H[d]
                h[centre]=1-sum(h[i] for i in leaves)
                key=canonical(h,[(i,centre) for i in leaves])
                counts=tuple(digits.count(d) for d in range(len(H)))
                columns[counts].append(key)
    return [columns[h] for h in hist]


def dfs_value(key,point):
    h,edges=key;vertices={i for edge in edges for i in edge};apex,=set(range(len(h)))-vertices
    adjacency={v:[] for v in vertices};oriented=set(edges);den=Q(1)
    for u,v in edges:adjacency[u].append(v);adjacency[v].append(u)
    def visit(v,parent):
        nonlocal den
        q,H=point[v],h[v]
        for child in adjacency[v]:
            if child==parent:continue
            qq,HH=visit(child,v);sg=1 if (child,v) in oriented else -1
            den*=(qq+point[apex]*HH)*(qq+point[apex]*(HH+sg))
            q+=qq;H+=HH
        return q,H
    visit(min(vertices),None)
    return Q((-point[apex])**(len(h)-4),den)


def main(n,reciprocal=False):
    started=time.monotonic();H=(-2,-1,Q(-1,2),0,1) if reciprocal else (-2,-1,0,1)
    hist=histograms(n-2,len(H))
    rng=random.Random(24102475+n);points=[];rows=[]
    while len(points)<len(hist)+10:
        point=[rng.randrange(1,70) for _ in range(n-1)];point.append(-sum(point))
        try: row=values(point,H,hist)
        except ZeroDivisionError:continue
        points.append(point);rows.append(row)
    mat=fmpq_mat([[str(q) for q in row] for row in rows]);reduced,rank=mat.rref()
    pivots=[next(j for j in range(len(hist)+1) if reduced[i,j]) for i in range(rank)]
    target_pivot=len(hist) in pivots
    data=dict(status='EXACT_SAMPLES_ONLY',n=n,head_values=list(map(str,H)),histograms=hist,points=points,
              rational_rows=[[str(q) for q in r] for r in rows],ranks=[rank-int(target_pivot),rank],
              producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('EXACT SAMPLE RANKS',data['ranks'],'COLUMNS',len(hist),'SECONDS',time.monotonic()-started,flush=True)
    orbits=family(n,H,hist)
    for row,point in zip(rows[:3],points[:3]):
        assert [sum((dfs_value(key,point) for key in orbit),Q(0)) for orbit in orbits]==row[:-1]
    chamber_controls=0
    for orbit in orbits:
        key=orbit[0]
        for point in points:
            try: chamber=chamber_value(key,point)
            except ZeroDivisionError:continue
            assert chamber==dfs_value(key,point);chamber_controls+=1;break
        else: raise AssertionError('no regular chamber-control point')
    data.update(independent_dfs_rows=3,chamber_controls=chamber_controls)
    checker=Verifier(budget=180)
    if not target_pivot:
        cs=[Q(0)]*len(hist)
        for i,p in enumerate(pivots):cs[p]=Q(str(reduced[i,len(hist)]))
        expr=exact_expression(n,orbits,cs)
        ok=checker.check(expr)
        data.update(status='EXACT_TOP_IDENTITY' if ok else 'EXACT_PROPOSAL_FAILED',coefficients=list(map(str,cs)))
    else:
        free=[j for j in range(len(hist)) if j not in pivots];kernels=[]
        forms=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
        for f in free:
            cs=[Q(0)]*len(hist);cs[f]=1
            for i,p in enumerate(pivots):
                if p<len(hist):cs[p]=-Q(str(reduced[i,f]))
            expr=exact_expression(n,orbits,cs)
            add(expr,(-1)**(n-1),(0,)*(n-1)+(1,),0,[(form,1) for form in forms])
            assert checker.check(expr)
            kernels.append([[j,str(c)] for j,c in enumerate(cs) if c])
        data.update(status='EXACT_GENERAL_HEAD_STAR_TOP_OBSTRUCTION',kernel_free_columns=free,kernel_vectors=kernels,
                    exact_kernel_count=len(kernels),ordinary_rank_upper=len(hist)-len(kernels))
    data.update(symbolic_calls=checker.calls,elapsed_seconds=time.monotonic()-started)
    path=HERE/f'overnight_upper_star_heads_{"reciprocal_" if reciprocal else ""}{n}.json';path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],'SECONDS',data['elapsed_seconds'],flush=True)


if __name__=='__main__':main(int(sys.argv[1]),len(sys.argv)>2 and sys.argv[2]=='reciprocal')
