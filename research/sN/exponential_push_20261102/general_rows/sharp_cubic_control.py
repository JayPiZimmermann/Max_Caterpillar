"""Exact finite checks of the O(N)-dictionary cubic sharpness family.

No unavailable SC'_2 certificate is loaded. These finite integer/rational
checks concern the actual local function and its Boolean values only.
"""
from itertools import combinations, product
from fractions import Fraction
from math import comb
from pathlib import Path
import json
import hashlib

OUT = Path(__file__).resolve().parent

def relu(x):
    return max(x, 0)

def inner(x):
    """a=0,b=1,c=2,z=3,t=4; unused coordinates are arbitrary."""
    return sum(relu(x[e]-x[0])+2*relu(x[e]-x[1])
               for e in range(2,len(x))) + relu(x[2]-x[0]+x[3]-x[4])-relu(x[3]-x[4])

def localized(x):
    """Local seven-input coordinates a,b,c plus four other selected leaves."""
    return sum(relu(x[e]-x[0])+2*relu(x[e]-x[1])
               for e in range(2,len(x)))+x[2]-x[0]

def boolean_g(B, n):
    return sum(int(e in B)*(int(0 not in B)+2*int(1 not in B))
               for e in range(2,n))+int(2 in B)-int(0 in B)

def all_subsets(n):
    return [frozenset(i for i,b in enumerate(bits) if b)
            for bits in product((0,1), repeat=n)]

result = {'status':'PASS', 'scope':'Finite exact controls, not an SCprime2 certificate or a network lower bound.', 'arity_checks':[]}
for n in range(4,10):
    subsets = all_subsets(n)
    # The full algebraic identity isolates the top interaction.
    for B in subsets:
        g = boolean_g(B,n)
        correction = int(B == {0})+int({0,1}<=B and 2 not in B)
        assert max(g,0) == g+correction
    mu = sum((-1)**(n-len(B))*max(boolean_g(B,n),0) for B in subsets)
    assert mu == (-1)**(n+1)
    # Every two-element vertex cover of K_{2,n-2} equals its hub pair.
    edges = [(a,e) for a in (0,1) for e in range(2,n)]
    covers = [A for A in subsets if len(A)<=2 and all(a in A or e in A for a,e in edges)]
    if n>=5:
        assert covers == [frozenset({0,1})]
        # Check the primitive anchor definition, not just its graph consequence.
        anchors = [A for A in subsets if len(A)<=2 and all(boolean_g(B,n)==0 for B in subsets if A<=B)]
        assert anchors == []
    assert boolean_g(frozenset(),n)==boolean_g(frozenset(range(n)),n)==0
    result['arity_checks'].append({'n':n,'top_mobius':mu,'coefficient_identity_subsets':len(subsets),
                                   'unique_two_cover':n>=5,'no_anchor_at_most_two':n>=5})

# Exact original nine-input preactivation controls. Selected a,b,c,5,6,7,8;
# the two auxiliary tail orders have identical actual survival and different offsets.
selected = (0,1,2,5,6,7,8)
for v_sign in (1,-1):
    q = [Fraction(0)]*9
    q[3],q[4] = ((-1,-3) if v_sign==1 else (-3,-1))
    assert inner(q)==0
    for ys in product((-1,0,1), repeat=7):
        eps=Fraction(1,100)
        point=q.copy()
        for i,y in zip(selected,ys): point[i]+=eps*y
        target=sum(relu(ys[e]-ys[0])+2*relu(ys[e]-ys[1]) for e in range(2,7))
        if v_sign==1: target+=ys[2]-ys[0]
        assert inner(point)==eps*target
result['actual_localization_checks']=2*3**7
result['probabilities']=[{'N':N,'p_exact':str(Fraction(comb(N-5,4),2*comb(N,7))),
                          'N_cubed_p':str(Fraction(N**3*comb(N-5,4),2*comb(N,7)))}
                         for N in (9,16,32,64,128,256,512,1024,4096)]
result['asymptotic_constant']=105
result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(OUT/'sharp_cubic_control.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','arity_checks':len(result['arity_checks']),
                  'actual_localization_checks':result['actual_localization_checks']}))
