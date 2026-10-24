#!/usr/bin/env python3
"""Cheap falsification: symmetrized tree Fourier functions at roots of unity.
Finite-field diagnostic only; nonzero values refute proposed zero-evaluation
invariant, while zero values need a symbolic proof. Prime m avoids subset
vanishing in characteristic zero. Producer: repository venv python this.py m.
"""
import sys,itertools,time,json
from pathlib import Path
import sympy as sp
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import dfs_review_fourier as f
m=int(sys.argv[1]);P=int(sp.nextprime(10**9))
while (P-1)%m:P=int(sp.nextprime(P))
z=pow(int(sp.primitive_root(P)),(P-1)//m,P);pt=[pow(z,i,P) for i in range(m)]
assert sum(pt)%P==0 and len(set(pt))==m
f.P=P;ps=list(itertools.permutations(range(m)));fam=f.family(m,'twin')
vals=[f.orbit_mod(u,pt,m,ps) for u in fam]
print(json.dumps({'m':m,'P':P,'zeta':z,'orbits':len(vals),'nonzero':sum(v!=0 for v in vals),'values':vals},indent=2))
