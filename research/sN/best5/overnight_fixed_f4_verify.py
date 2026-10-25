"""Independent exact verification of the F4 positive-fold obstruction.

No numerical solver, producer import, group inventory, or certificate file
is used. The orbit is built from three explicit orthogonal frames.
"""
from fractions import Fraction as Q
from itertools import product,combinations
import hashlib,json,math
from pathlib import Path


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def canonical(v):
    d=math.gcd(*v)
    assert d
    if next(x for x in v if x)<0:d=-d
    return tuple(x//d for x in v)
def function(A):return tuple(sorted(A))
def compose(A,B):
    # All stored rows/matrices are twice the actual transformation.
    values=[tuple(sum(a[k]*B[k][j] for k in range(4)) for j in range(4)) for a in A]
    assert all(v%2==0 for row in values for v in row)
    return function(tuple(tuple(v//2 for v in row) for row in values))
def q(A,x):return Q(max(0,min(dot(a,x) for a in A)),2)


def main():
    I=tuple(tuple(2*int(i==j) for j in range(4)) for i in range(4))
    frames=[I,((1,-1,-1,-1),(1,-1,1,1),(1,1,-1,1),(1,1,1,-1)),((1,-1,-1,1),(1,-1,1,-1),(1,1,-1,-1),(1,1,1,1))]
    for A in frames:assert [[dot(a,b) for b in A] for a in A]==[[4*int(i==j) for j in range(4)] for i in range(4)]
    functions={function(tuple(tuple(s*v for v in row) for row,s in zip(A,signs))) for A in frames for signs in product((-1,1),repeat=4)}
    assert len(functions)==48
    generators=[]
    for k in range(3):
        p=list(range(4));p[k],p[k+1]=p[k+1],p[k]
        generators.append(tuple(tuple(2*int(p[i]==j) for j in range(4)) for i in range(4)))
    generators.extend((tuple(tuple((-2 if i==j==0 else 2*int(i==j)) for j in range(4)) for i in range(4)),((1,1,1,1),(1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1))))
    assert all(compose(A,B) in functions for A in functions for B in generators)
    orbit={function(I)};front=list(orbit)
    while front:
        A=front.pop()
        for B in generators:
            C=compose(A,B)
            if C not in orbit:orbit.add(C);front.append(C)
    assert orbit==functions
    walls={tuple(int(i==j) for j in range(4)) for i in range(4)}
    walls|={tuple(int(k==i)+s*int(k==j) for k in range(4)) for i,j in combinations(range(4),2) for s in(-1,1)}
    walls|={(1,)+s for s in product((-1,1),repeat=3)}
    assert len(walls)==24
    actual={canonical(row) for A in functions for row in A}
    actual|={canonical(tuple(a-b for a,b in zip(A[i],A[j]))) for A in functions for i,j in combinations(range(4),2)}
    assert actual==walls
    points=((0,0,1,1),(0,1,1,0),(0,1,1,2),(1,0,1,0),(1,0,1,2),(1,1,2,0),(1,1,1,3))
    coeff=(-1,-1,1,-1,1,1,-1)
    assert all(sum(c*x[j] for c,x in zip(coeff,points))==0 for j in range(4))
    assert all(sum(c*abs(dot(h,x)) for c,x in zip(coeff,points))==0 for h in walls)
    assert all(q(A,x)==0 for A in functions for x in points[:-1])
    positive=[A for A in sorted(functions) if q(A,points[-1])]
    assert len(positive)==2 and function(I) in positive
    assert all(q(A,points[-1])==1 for A in positive)
    assert all(all(v>=0 for v in x) for x in points)
    report={'status':'PASS_EXACT_F4_ANY_SHALLOW_POSITIVE_FOLD_EXCLUSION','orbit_functions':48,'orthogonal_frames':3,'potential_hyperplanes':24,'functional_points':points,'functional_coefficients':coeff,'nonzero_functions_at_interior_point':positive,'interior_values':['1','1'],'scope':'Together with the wall-elimination argument in the note, no nonzero nonnegative combination of the48 orbit functions equals one ReLU of any finite shallow preactivation, with arbitrary real first-layer directions.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path('overnight_fixed_f4_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
