#!/usr/bin/env python3
"""Smallest actual Baxter-class / union-zonotope top-kernel bridge test.

The target is the original signed caterpillar sum over a nontrivial twin-BST
class. Sources are every top face state of the union four-cycle, with
canonical root heads. This tests a concrete bridge, not a counting analogy.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,permutations,product
from pathlib import Path
import hashlib,json,random,time
from flint import nmod_mat

HERE=Path(__file__).parent;PRIME=1000000007

def bst(word):
    if not word:return ()
    root=word[0];left=tuple(x for x in word[1:] if x<root);right=tuple(x for x in word[1:] if x>root)
    edges=list(bst(left)+bst(right))
    if left:edges.append((root,left[0]))
    if right:edges.append((root,right[0]))
    return tuple(sorted(edges))

def normalize(n,head,edges):
    head=list(head);normalized=[]
    for u,v in edges:
        if u>v:
            head[u]+=1;head[v]-=1
            u,v=v,u
        normalized.append((u,v))
    return tuple(head),tuple(sorted(normalized))

def word_target(n,word):
    out=defaultdict(int)
    for mask in range(1,1<<(n-2)):
        spine=[0]+[j for j in range(1,n-1) if mask>>(j-1)&1]
        edges=[]
        for j in range(1,n-1):
            parent=max(i for i in spine if i<j)
            edges.append((word[parent],word[j]))
        head=[0]*n;head[0]=-1;head[word[max(spine)]]=1
        out[normalize(n,head,edges)]+=(-1)**(n+mask.bit_count())
    return dict(out)

def factors(n,unit):
    head,edges=unit;reference=1
    adjacency={v:[] for v in range(1,n)}
    for u,v in edges:adjacency[u].append(v);adjacency[v].append(u)
    result=[]
    for u,v in edges:
        stack=[v];seen={v}
        while stack:
            w=stack.pop()
            for z in adjacency[w]:
                if {w,z}=={u,v} or z in seen:continue
                seen.add(z);stack.append(z)
        away=seen if reference not in seen else set(range(1,n))-seen
        epsilon=1 if u in away else -1
        H=sum(head[i] for i in away)
        q=tuple(int(i in away) for i in range(n))
        result += [tuple(q[i]+int(i==0)*H for i in range(n)),
                   tuple(q[i]+int(i==0)*(H+epsilon) for i in range(n))]
    return tuple(result)

def value(n,forms,point,p):
    denominator=1
    for f in forms:
        v=sum(a*b for a,b in zip(f,point))%p
        if not v:raise ZeroDivisionError
        denominator=denominator*v%p
    return pow(-point[0]%p,n-4,p)*pow(denominator,-1,p)%p

def reconstruct(a,p):
    # Classical bounded rational reconstruction; a proposal, not a proof.
    bound=int((p//2)**.5);r0,r1=p,int(a);t0,t1=0,1
    while abs(r1)>bound:
        q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
    if not t1 or abs(t1)>bound:return None
    answer=Q(r1,t1)
    if answer.denominator%p and answer.numerator*pow(answer.denominator,-1,p)%p==a:return answer
    return None

def main():
    start=time.monotonic();n=5;groups=defaultdict(list)
    for word in permutations(range(1,n)):groups[(bst(word),bst(word[::-1]))].append(word)
    pair,words=next((pair,words) for pair,words in sorted(groups.items()) if len(words)>1)
    union=tuple(sorted(set(tuple(sorted(e)) for tree in pair for e in tree)))
    assert len(words)==2 and len(union)==4
    target=defaultdict(int)
    for word in words:
        for unit,c in word_target(n,word).items():target[unit]+=c
    target={u:c for u,c in target.items() if c}
    sources=set()
    for omitted in union:
        remaining=[e for e in union if e!=omitted]
        for root in range(1,n):
            for shift in (-1,0,1):
                for signs in product((-1,1),repeat=len(remaining)):
                    head=[0]*n;head[0]=-1;head[root]=1
                    head[omitted[0]]+=shift;head[omitted[1]]-=shift
                    edges=[(u,v) if sign==1 else (v,u) for (u,v),sign in zip(remaining,signs)]
                    sources.add(normalize(n,head,edges))
    sources=sorted(sources);source_forms=[factors(n,u) for u in sources]
    target_forms=[(factors(n,u),c) for u,c in target.items()]
    rng=random.Random(25102547);points=[];rows=[]
    while len(rows)<len(sources)+12:
        values=[rng.randrange(1,20000) for _ in range(n-1)];point=[-sum(values)]+values
        try:
            row=[value(n,f,point,PRIME) for f in source_forms]
            rhs=sum(c*value(n,f,point,PRIME) for f,c in target_forms)%PRIME
        except ZeroDivisionError:continue
        points.append(point);rows.append(row+[rhs])
    rr,rank=nmod_mat(rows,PRIME).rref()
    pivots=[next(j for j in range(len(sources)+1) if rr[i,j]) for i in range(rank)]
    gap=len(sources) in pivots
    result=dict(status='MODULAR_BAXTER_UNION_BRIDGE_GAP' if gap else 'MODULAR_BAXTER_UNION_BRIDGE_INCLUSION',
                labels=n,twin_pair=pair,class_words=words,union_graph=union,
                sources=sources,target=[[u,c] for u,c in target.items()],
                source_columns=len(sources),target_units=len(target),points=points,
                prime=PRIME,ranks=[rank-int(gap),rank],
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                scope='Smallest nontrivial twin-BST class versus the complete canonical four-cycle top face family. Modular status only until a rational-function gate passes.')
    if not gap:
        solution=[0]*len(sources)
        for i,j in enumerate(pivots):solution[j]=int(rr[i,len(sources)])
        proposal=[reconstruct(v,PRIME) for v in solution]
        result.update(modular_solution=solution,
                      rational_proposal=None if any(v is None for v in proposal) else list(map(str,proposal)))
    result['seconds']=time.monotonic()-start
    (HERE/'overnight_upper_baxter_union.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'CLASS',words,'COLUMNS',len(sources),'RANKS',result['ranks'],
          'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
