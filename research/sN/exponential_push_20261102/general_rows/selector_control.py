"""Exact actual-network/Good/Q controls for the adaptive selector obstruction.

All gate coefficients and sampled gap points are integers. Neighborhood tests
use Fraction. No SCprime2 certificate is assumed, reconstructed or evaluated.
"""
from itertools import permutations, combinations
from fractions import Fraction
from pathlib import Path
import math
import json
import hashlib

OUT=Path(__file__).resolve().parent

def row(N, terms):
    out=[0]*N
    for i,w in terms: out[i]+=w
    return tuple(out)

def dictionary(N,P):
    a,b,z,t=0,1,2,3
    gates=[]
    for e in range(N):
        if e not in (a,b):
            gates.extend(((1,row(N,((e,1),(a,-1)))),
                          (2,row(N,((e,1),(b,-1))))))
    for c in P:
        gates.append((1,row(N,((c,1),(a,-1),(z,1),(t,-1)))))
    gates.append((-1,row(N,((z,1),(t,-1)))))
    return gates

def dot(w,x): return sum(a*b for a,b in zip(w,x))
def inner(gates,x): return sum(o*max(dot(w,x),0) for o,w in gates)
def support(w):return frozenset(i for i,a in enumerate(w)if a)

def adjacent(G,a,b):return abs(a-b)==1 and max(a,b)in G
def same_run(G,a,b):return all(i in G for i in range(min(a,b)+1,max(a,b)+1))
def anchor(G,a):return all(i in G for i in range(a+1))

def support_bad(T,S,tau,G):
    """Primitive original-label role placement; independent of activation signs."""
    if len(T)<4:return False
    inv={i:p for p,i in enumerate(tau)}
    for cherry in combinations(T,2):
        if any(i in S for i in cherry):continue
        x,y=map(inv.__getitem__,cherry)
        if not adjacent(G,x,y):continue
        others=T-set(cherry)
        # A: another unordered tail pair in one Gamma run.
        for z,t in combinations(others,2):
            if z not in S and t not in S and same_run(G,inv[z],inv[t]):return True
        # B: one selected support label and a third tail in the anchor run.
        if any(s in S for s in others):
            if any(z not in S and anchor(G,inv[z]) for z in others):return True
        # C: a disjoint selected support pair.
        if len(others&S)>=2:return True
    return False

def isolated(G,m):
    return frozenset(g for g in G if g!=0 and g-1 not in G and g+1 not in G)

def Gvalue(B,S,c):
    return sum(int(e in B)*(int(0 not in B)+2*int(1 not in B))
               for e in S if e not in(0,1))+int(c in B)-int(0 in B)

reports=[]
for N,r in ((11,2),(12,3)):
    P=frozenset(range(4,4+r))
    c=min(P)
    neutral=[i for i in range(N)if i not in P|{0,1,2,3}]
    S=frozenset((0,1,c,*neutral[:4]))
    tail=tuple(i for i in range(N)if i not in S)
    m=len(tail)
    gates=dictionary(N,P)
    assert len(gates)==2*N-3+r
    assert all(sum(w)==0 for _,w in gates)
    assert all(not support(w)<=S for _,w in gates if len(support(w))>=3)
    byK={K:{'base':0,'with_enough':0,'restricted_base':0,'restricted_with_enough':0,'raw_space':math.factorial(m)**2}
         for K in range(1,m)}
    local_checked=False
    for tau in permutations(tail):
        pz,pt=tau.index(2),tau.index(3)
        if not(0<=pz and pt-pz>=2):continue
        interval=tuple(range(pz+1,pt+1))
        for rho in permutations(range(m)):
            H=rho[0]
            if not all(rho[g]<H for g in interval):continue
            q=[0]*N
            distance=0
            for i,label in enumerate(tau):
                distance+=4**rho[i]
                q[label]=-distance
            assert 0<q[2]-q[3]<4**H
            assert inner(gates,q)==0
            V=[0]*N
            for o,w in gates:
                d=dot(w,q)
                if not support(w)<=S:assert d!=0
                if d>0:
                    V=[a+o*b for a,b in zip(V,w)]
            expected=[int(i==c)-int(i==0)for i in range(N)]
            assert V==expected
            assert all(V[i]==0 for i in tail)
            # Every tail subset, hence every prefix in every order, vanishes.
            assert all(sum(V[i]for i in B)==0
                       for k in range(m+1)for B in combinations(tail,k))
            for K,data in byK.items():
                if H<K:continue
                Gamma=frozenset(g for g in range(m)if rho[g]<K)
                assert 0 not in Gamma
                assert not any(support_bad(support(w),S,tau,Gamma)
                               for _,w in gates)
                data['base']+=1
                restricted=tau[0]in P and pz>=1
                if restricted:data['restricted_base']+=1
                if 2*len(isolated(Gamma,m))>=K:
                    data['with_enough']+=1
                    if restricted:data['restricted_with_enough']+=1
            if not local_checked:
                eps=Fraction(1,100)
                for k in range(8):
                    for B in combinations(S,k):
                        B=frozenset(B)
                        x=[Fraction(v)for v in q]
                        for i in B:x[i]+=eps
                        assert inner(gates,x)==eps*Gvalue(B,S,c)
                local_checked=True
    assert local_checked
    # Independent formula count of tail/rank events, before imposing Q.
    for K,data in byK.items():
        exact=sum(
            Fraction(m-d,m*(m-1)*(d+1))*
            (1-Fraction(math.prod(range(K-d,K+1)),math.prod(range(m-d,m+1))))
            for d in range(2,m))
        # math.prod interval containing 0 correctly gives the zero falling factorial.
        assert Fraction(data['base'],data['raw_space'])==exact
        restricted_exact=Fraction(r-1,m)*sum(
            Fraction(m-d-1,(m-1)*(m-2)*(d+1))*
            (1-Fraction(math.prod(range(K-d,K+1)),math.prod(range(m-d,m+1))))
            for d in range(2,m-1))
        assert Fraction(data['restricted_base'],data['raw_space'])==restricted_exact
    reports.append({'N':N,'P_size':r,'S':sorted(S),'gate_count':len(gates),
                    'conditional_selected_set_counts':byK})
result={'status':'PASS','scope':'Exact finite actual ReLU/active-gradient/local-Boolean and literal A/B/C Good/Q controls; the all-N asymptotic proof is in SELECTOR.md, not a Lean theorem.',
        'cases':reports,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(OUT/'selector_control.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','N_cases':len(reports),'actual_configurations':sum(sum(d['base']for d in r['conditional_selected_set_counts'].values())for r in reports)}))
