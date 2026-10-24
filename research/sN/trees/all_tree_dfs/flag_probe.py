#!/usr/bin/env python3
"""Canonical-root tree pyramids in the top support-function quotient.
Exact integer flag evaluations; rank is measured modulo a prime, separation
must be certified over Q separately. Seed 24024. Run: python3 .../flag_probe.py
A flag is m-2 successive max-minus-min exposed-face differences, followed
by width in one direction. This annihilates L_{m-2}. Columns are S_m orbit
sums of canonical-root oriented stars, no arbitrary heads allowed.
"""
import itertools, json, time, sys
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from flag_test import pyramid
from pn_test import rank_mod_p

def orbit_reps(m):
    # apex 0, centre 1, leaves 2..m-1; root centre or first leaf
    out=[]
    for root in [1,2]:
        distinguished=[] if root==1 else [root]
        rest=[v for v in range(2,m) if v!=root]
        for ds in itertools.product([0,1],repeat=len(distinguished)):
            for k in range(len(rest)+1):
                directions=dict(zip(distinguished,ds))
                directions.update({v:int(j<k) for j,v in enumerate(rest)})
                E=[(v,1) if directions[v] else (1,v) for v in range(2,m)]
                h=[0]*m;h[0]=-1;h[root]=1
                out.append((root,ds,k,np.array(pyramid(m,h,E),dtype=np.int64)))
    return out

def tau(G,U,w):
    if len(G)==1:return 0
    if not U:
        v=G@w;return int(v.max()-v.min())
    v=G@U[0];lo=v.min();hi=v.max()
    if lo==hi:return 0
    return tau(G[v==hi],U[1:],w)-tau(G[v==lo],U[1:],w)

def main():
    m=int(sys.argv[1]) if len(sys.argv)>1 else 5
    ntests=int(sys.argv[2]) if len(sys.argv)>2 else 80
    rng=np.random.default_rng(24024)
    reps=orbit_reps(m); perms=list(itertools.permutations(range(m)))
    orbits=[[g[:,p] for p in perms] for _,_,_,g in reps]
    I=np.eye(m,dtype=np.int64)
    simplex=I.copy()
    rows=[];targets=[];flags=[]
    for j in range(ntests):
        # Facet directions: arbitrary two-value cuts, and 2 at apex,
        # 1 on root component, 0 on opposite component.
        while True:
            u=rng.integers(0,3,size=m) if j%2 else rng.integers(0,2,size=m)
            inds=rng.permutation(m)[:m-2]
            U=[u]+[I[i] for i in inds[:m-3]]
            w=I[inds[m-3]]
            if np.linalg.matrix_rank(np.array([[1]*m]+U+[w],dtype=float))==m:break
        row=[sum(tau(g,U,w) for g in orbit) for orbit in orbits]
        target=tau(simplex,U,w)*len(perms)
        rows.append(row);targets.append(target)
        flags.append({'U':[u.tolist() for u in U],'w':w.tolist()})
        if (j+1)%10==0:
            A=np.array(rows,dtype=np.int64);B=np.column_stack([A,targets])
            print(f'{j+1} flags: rank {rank_mod_p(A)}; with max {rank_mod_p(B)}',flush=True)
    data={'m':m,'seed':24024,'reps':[{'root':r,'root_edge':ds,'out_count':k} for r,ds,k,_ in reps], 'A':rows,'b':targets,'flags':flags}
    out=Path(__file__).with_name(f'flags_{m}.json');out.write_text(json.dumps(data,indent=2)+'\n')
    import sympy as sp
    A=sp.Matrix(rows);b=sp.Matrix(targets)
    print('RATIONAL ranks',A.rank(),A.row_join(b).rank(),flush=True)
    for c in A.T.nullspace():
        value=(c.T*b)[0]
        if value:
            cert={'weights':[str(t/value) for t in c],'target':1}
            out.with_name(f'flag_separator_{m}.json').write_text(json.dumps(cert,indent=2)+'\n')
            print('EXACT separator saved',flush=True);break
if __name__=='__main__':main()
