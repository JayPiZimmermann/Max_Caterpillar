"""Exact seven-point obstruction for the signed six-term F4 state."""
from fractions import Fraction as Q
from itertools import combinations,product
import hashlib,json
from pathlib import Path


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def pieces():
    base=[tuple(2*int(i==j)for j in range(4))for i in range(4)]
    balanced=[tuple(1-2*int(i==j)for j in range(4))for i in range(4)]
    dominant=[[(1,1,1,1)]+[tuple(2*int(k in(i,j))-1 for k in range(4))for j in range(4)if j!=i]for i in range(4)]
    return [(-1,base),(1,balanced)]+[(1,A)for A in dominant]
def value(x):return sum(w*Q(max(0,min(dot(a,x)for a in A)),2)for w,A in pieces())
def derivative(x,v):
    out=Q(0)
    for w,A in pieces():
        vals=[dot(a,x)for a in A];m=min(vals);d=min(dot(a,v)for a,t in zip(A,vals)if t==m)
        out+=w*Q(d if m>0 else max(0,d)if m==0 else 0,2)
    return out


def main():
    points=((0,0,1,1),(0,-1,0,1),(0,-1,2,1),(-1,0,0,1),(-1,0,2,1),(-1,-1,0,2),(-1,-1,3,1));coeff=(-1,-1,1,-1,1,1,-1);directions=(1,1,-1,1,-1,1)
    walls={tuple(int(i==j)for j in range(4))for i in range(4)}|{tuple(int(k==i)+s*int(k==j)for k in range(4))for i,j in combinations(range(4),2)for s in(-1,1)}|{(1,)+s for s in product((-1,1),repeat=3)}
    assert len(walls)==24
    assert all(sum(c*x[j]for c,x in zip(coeff,points))==0 for j in range(4))
    assert all(sum(c*abs(dot(h,x))for c,x in zip(coeff,points))==0 for h in walls)
    assert [value(x)for x in points]==[0,0,0,0,0,0,1]
    assert [derivative(x,(0,0,0,s))for x,s in zip(points,directions)]==[Q(1,2)]*6
    assert sum(c*value(x)for c,x in zip(coeff,points))==-1
    report={'status':'PASS_EXACT_SIGNED_F4_SEVEN_POINT_NO_FOLD','points':points,'feature_identity_coefficients':coeff,'target_values':['0']*6+['1'],'boundary_positive_directions_in_coordinate4':directions,'boundary_derivatives':['1/2']*6,'potential_walls':24,'scope':'Together with the analytic classification of hyperplanes in the zero set, this excludes every finite shallow preactivation, with arbitrary real directions and biases.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path('overnight_fixed_f4_signed_nofold_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
