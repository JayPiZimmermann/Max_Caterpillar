#!/usr/bin/env python3
"""Independent replay of scalar conversion and the two positive bridges.

Forest kernels are derived by inverse coordinate matrices, without the
producer's cut sums or zonotope tiling. BSTs are reconstructed by insertion.
Only the compact receipts are needed, not the 18MB NC search inventory.
"""
from collections import defaultdict,Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,sys,time
from flint import fmpq_mat
HERE=Path(__file__).parent;sys.path.insert(0,str(HERE/'all_tree_dfs'))
from rational_identity import term,Verifier

def scalar_identities():
    # ReLU arguments are formal pairs (coefficient of A, coefficient of y).
    # For each sign of y, inner ReLUs become linear; no sign of A is assumed.
    checks=[]
    for positive in (False,True):
        z=int(positive);minus_z=int(not positive)
        # sigma(A-sigma(y))=sigma(A)+sigma(A-y)-sigma(A+sigma(-y)).
        lhs=Counter({(1,-z):1})
        rhs=Counter({(1,0):1});rhs[(1,-1)]+=1;rhs[(1,-minus_z)]-=1
        assert {k:v for k,v in lhs.items() if v}=={k:v for k,v in rhs.items() if v}
        # sigma(A+2sigma(y))=sigma(A+sigma(y))+sigma(A+y+sigma(y))-sigma(A+y).
        lhs=Counter({(1,2*z):1})
        rhs=Counter({(1,z):1});rhs[(1,1+z)]+=1;rhs[(1,1)]-=1
        assert {k:v for k,v in lhs.items() if v}=={k:v for k,v in rhs.items() if v}
        checks.extend([['negative',positive],['length_two',positive]])
    return checks

def matrix_term(n,head,edges):
    forms=[head]+[tuple(int(i==u)-int(i==v) for i in range(n)) for u,v in edges]
    B=fmpq_mat([list(f[1:]) for f in forms]);det=Q(str(B.det()));assert det
    inv=B.inv()
    dual=[tuple(Q(str(inv[i,j])) for i in range(n-1))+(Q(0),) for j in range(n-1)]
    A=dual[0];den=[]
    for b in dual[1:]:den.extend([(b,1),(tuple(x-y for x,y in zip(b,A)),1)])
    return term(1/abs(det),A,n-4,den)

def subtract_simplex(expr,n):
    forms=[(-1,)*(n-1)+(0,)]+[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]
    key,c=term((-1)**(n-1),(0,)*(n-1)+(1,),0,[(f,1) for f in forms])
    expr[key]-=c

def insert_bst(word):
    root=None;children={};edges=[]
    for v in word:
        children[v]=[None,None]
        if root is None:root=v;continue
        u=root
        while True:
            side=int(v>u)
            if children[u][side] is None:children[u][side]=v;edges.append(tuple(sorted((u,v))));break
            u=children[u][side]
    return set(edges)

def main():
    start=time.monotonic();scalar=scalar_identities()
    max5path=HERE/'overnight_upper_baxter_max5_control.json';m=json.loads(max5path.read_text())
    expr=defaultdict(Q)
    for row in m['forests']:
        key,c=matrix_term(5,row['head'],row['edges']);expr[key]+=Q(row['coefficient'])*c
    subtract_simplex(expr,5);v5=Verifier(budget=150);assert v5.check(dict(expr))
    print('INVERSE MATRIX MAX5 PASSED',len(m['forests']),'SECONDS',time.monotonic()-start,flush=True)
    ncpath=HERE/'overnight_upper_baxter_nc7_embedding.json';r=json.loads(ncpath.read_text());expr=defaultdict(Q)
    direct=reflected=0;graphs=set()
    for a,root,edges,coefficient,b,word,reflection in r['compact_atoms']:
        assert sorted(word)==[v for v in range(7) if v!=b]
        graph=insert_bst(word)|insert_bst(word[::-1])|{tuple(sorted((b,v))) for v in range(7) if v!=b}
        assert all(tuple(sorted(e)) in graph for e in edges)
        assert len(edges)==5 and all(a not in e for e in edges)
        if reflection:
            assert b==root;reflected+=1
            candidate_head=[int(i==a)-int(i==root) for i in range(7)]
            candidate_edges=[(v,u) for u,v in edges]
            sign=-1
        else:
            assert b!=root;direct+=1
            candidate_head=[int(i==root)-int(i==b) for i in range(7)]
            if b!=a:
                assert tuple(sorted((b,a))) in graph
                candidate_head[b]+=1;candidate_head[a]-=1
            candidate_edges=edges;sign=1
            assert candidate_head==[int(i==root)-int(i==a) for i in range(7)]
        # Compute the EMBEDDED candidate, including reflection parity.
        key,c=matrix_term(7,candidate_head,candidate_edges)
        expr[key]+=sign*Q(coefficient)*c
        graphs.add((b,tuple(sorted(graph))))
    assert direct==r['direct_embeddings'] and reflected==r['top_reflection_embeddings']
    subtract_simplex(expr,7);v7=Verifier(budget=150);assert v7.check(dict(expr))
    result=dict(status='INDEPENDENT_EXACT_BAXTER_POSITIVE_BRIDGES_PASSED',
        scalar_formal_sign_cases=scalar,max5_forest_atoms=len(m['forests']),max5_principal_parts=v5.calls,
        nc7_direct=direct,nc7_reflected=reflected,nc7_used_graphs=len(graphs),nc7_principal_parts=v7.calls,
        max5_receipt_sha256=hashlib.sha256(max5path.read_bytes()).hexdigest(),
        nc7_receipt_sha256=hashlib.sha256(ncpath.read_bytes()).hexdigest(),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
        independence='Coordinate-matrix inversion replaces all graph-cut Fourier formulas; iterative BST insertion replaces recursive BST splitting. Shared exact rational identity engine is an audited principal-part algorithm.',
        scope='The scalar conversions are whole-function identities. The graphic forests and reflected NC7 embeddings certify top-class identities; lower-dimensional network corrections remain separate.')
    (HERE/'overnight_upper_baxter_bridge_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
