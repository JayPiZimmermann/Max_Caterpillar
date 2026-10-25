"""Independent exact counterexample to the proposed signed-root score Q_*.

Standard library only. Does not import the score producer or numerical gate.
Rooted signed extension counts are enumerated directly, and the local
rational identity is checked by integer common-denominator arithmetic.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict,Counter
import itertools,json,time

COMMON=[(5,2),(2,7),(4,3),(6,5),(7,8)]
EXTRA=[[(2,1),(1,3)],[(1,2),(3,1)],[(3,1),(2,3)],
       [(2,1),(3,2)],[(1,3),(3,2)],[(1,2),(2,3)]]
WEIGHTS=[1,-1,-1,1,1,-1]
EXPECTED=[3300,300,0,660,0,3900]

def polynomial(forms):
    p={(0,0,0):1}
    for f in forms:
        out=defaultdict(int)
        for m,c in p.items():
            for j,a in enumerate(f):
                if a:
                    n=list(m);n[j]+=1;out[tuple(n)]+=a*c
        p=dict(out)
    return p

def local_identity():
    x=(1,0,0);y=(0,1,0);z=(1,1,0)
    shift=lambda q,e:(q[0],q[1],e)
    factors=[x,y,z]+[shift(q,e)for q in(x,y,z)for e in(-1,1)]
    specifications=[[(x,1),(y,-1)],[(x,-1),(y,1)],
                    [(z,1),(x,1)],[(z,1),(y,1)],
                    [(z,-1),(x,-1)],[(z,-1),(y,-1)]]
    numerator=defaultdict(int)
    for w,spec in zip(WEIGHTS,specifications):
        den=Counter(factors)
        for q,e in spec:den.subtract([q,shift(q,e)])
        assert min(den.values())>=0
        for m,c in polynomial(list(den.elements())).items():numerator[m]+=w*c
    assert not any(numerator.values())
    return specifications

def data(edges):
    T={v:set()for v in range(1,9)}
    for v,w in edges:T[v].add(w);T[w].add(v)
    parent={1:None};todo=[1]
    for v in todo:
        for w in sorted(T[v]):
            if w!=parent[v]:
                assert w not in parent
                parent[w]=v;todo.append(w)
    assert len(todo)==8
    cut={}
    for v in reversed(todo[1:]):
        C={v};stack=[v]
        for w in stack:
            for j in T[w]:
                if parent.get(j)==w:C.add(j);stack.append(j)
        cut[frozenset((v,parent[v]))]=(frozenset(C),1 if(v,parent[v])in edges else -1)
    return T,parent,cut

def signed_extensions(T):
    I={v:0 for v in T}
    for p in itertools.permutations(sorted(T)):
        seen={p[0]}
        for v in p[1:]:
            if not(T[v]&seen):break
            seen.add(v)
        else:
            inversions=sum(p[i]>p[j]for i in range(8)for j in range(i+1,8))
            I[p[0]]+=(-1)**inversions
    return I

def independent_score(edges,T,parent,I):
    kappa={v:int(v==1)+sum(a==v for a,b in edges)for v in T}
    chi={1:1};todo=[1];epsilon=1
    for v in todo:
        for w in T[v]:
            if parent.get(w)==v:
                todo.append(w);chi[w]=-chi[v];epsilon*=1 if(w,v)in edges else -1
    sums=defaultdict(int)
    for v in T:
        dist={v:0};todo=[v]
        for w in todo:
            for j in T[w]:
                if j not in dist:dist[j]=dist[w]+1;todo.append(j)
        for w in T:
            f=I[v]*I[w]*dist[w];h=chi[v]*chi[w];k=kappa[v]+kappa[w]
            sums['D1']+=f;sums['D2']+=f*dist[w]
            sums['K1']+=f*k;sums['D1chi']+=f*h;sums['K1chi']+=f*k*h
    score=Q(15,8)*(36*sums['D1']-2*sums['K1']+2*epsilon*sums['D1']-6*sums['K1chi']-2*epsilon*sums['D1chi']-3*epsilon*sums['D2'])
    return score,dict(kappa=kappa,epsilon=epsilon,moments=dict(sums))

def main():
    start=time.monotonic();specs=local_identity();A=frozenset((2,5,6,7,8));B=frozenset((3,4));sets={(1,0):A,(0,1):B,(1,1):A|B};results=[];common=None
    for extra,expected,spec,w in zip(EXTRA,EXPECTED,specs,WEIGHTS):
        edges=COMMON+extra;T,parent,cuts=data(edges)
        fixed={frozenset(e):cuts[frozenset(e)]for e in COMMON}
        if common is None:common=fixed
        assert fixed==common
        special=Counter(cuts[frozenset(e)]for e in extra)
        assert special==Counter((sets[q[:2]],e)for q,e in spec)
        I=signed_extensions(T);value,moments=independent_score(edges,T,parent,I)
        assert value==expected
        results.append(dict(root=1,edges=edges,coefficient=w,signed_root_counts=I,score=str(value),**moments))
    pairing=sum(w*s for w,s in zip(WEIGHTS,EXPECTED));assert pairing==-240
    out=dict(status='INDEPENDENT_EXACT_Q_STAR_REFUTATION_N9',arity=9,
             rational_identity_numerator_zero=True,common_cut_factors_identical=True,
             independent_connected_prefix_enumeration=True,score_pairing=pairing,terms=results,
             scope='The six individual kernels have an exact rational identity for every generic frequency. Full label symmetrization preserves it. Q_* assigns a nonzero value to that identity, so this formula cannot define a linear separator on the actual rational-function space. This does not refute the perfect-matching separator conjecture or the unrestricted exponential lower bound.',
             seconds=time.monotonic()-start)
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
