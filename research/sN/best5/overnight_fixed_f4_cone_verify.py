"""Independent exact nonnegative-cone counterexample on the F4 fan."""
from fractions import Fraction as Q
from itertools import product,combinations
import hashlib,json,math
from pathlib import Path


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def kernel3(rows):
    A=[[Q(x)for x in row]for row in rows];pivots=[]
    for col in range(4):
        rank=len(pivots);p=next((i for i in range(rank,3)if A[i][col]),None)
        if p is None:continue
        A[rank],A[p]=A[p],A[rank];v=A[rank][col];A[rank]=[x/v for x in A[rank]]
        for i in range(3):
            if i==rank:continue
            v=A[i][col];A[i]=[x-v*y for x,y in zip(A[i],A[rank])]
        pivots.append(col)
        if len(pivots)==3:break
    if len(pivots)<3:return None
    free=next(j for j in range(4)if j not in pivots);v=[Q(j==free)for j in range(4)]
    for i,j in enumerate(pivots):v[j]=-A[i][free]
    den=math.lcm(*(x.denominator for x in v));v=[int(x*den)for x in v];d=math.gcd(*v)
    if next(x for x in v if x)<0:d=-d
    return tuple(x//d for x in v)


def main():
    I=tuple(tuple(2*int(i==j)for j in range(4))for i in range(4));A1=((1,-1,-1,-1),(1,-1,1,1),(1,1,-1,1),(1,1,1,-1));A2=((1,-1,-1,1),(1,-1,1,-1),(1,1,-1,-1),(1,1,1,1));classes={}
    for k,A in enumerate((I,A1,A2)):
        for signs in product((-1,1),repeat=4):
            f=tuple(sorted(tuple(s*v for v in row)for s,row in zip(signs,A)));classes[f]=(k,math.prod(signs))
    functions=sorted(classes);base=functions.index(tuple(sorted(I)));balanced=tuple(sorted(tuple(1-2*int(i==j)for j in range(4))for i in range(4)));dominant=[]
    for i in range(4):dominant.append(tuple(sorted([(1,1,1,1)]+[tuple(2*int(k in(i,j))-1 for k in range(4))for j in range(4)if j!=i])))
    positive=[functions.index(A)for A in dominant+[balanced]];assert len(set(positive))==5;weights=[int(i in positive)-int(i==base)for i in range(48)]
    rel=[]
    for plus,minus in(((0,1),(2,1)),((0,-1),(1,1)),((2,-1),(1,-1))):rel.append([int(classes[f]==plus)-int(classes[f]==minus)for f in functions])
    null=[rel[0][i]-rel[1][i]+rel[2][i]for i in range(48)];assert set(null)=={-1,1} and null[base]==1
    other=next(i for i in range(48)if null[i]==-1 and weights[i]==0)
    assert weights[base]==-1 and weights[other]==0
    walls={tuple(int(i==j)for j in range(4))for i in range(4)}|{tuple(int(k==i)+s*int(k==j)for k in range(4))for i,j in combinations(range(4),2)for s in(-1,1)}|{(1,)+s for s in product((-1,1),repeat=3)}
    lines={v for triple in combinations(sorted(walls),3)if(v:=kernel3(triple))is not None};rays=sorted(tuple(s*x for x in v)for v in lines for s in(-1,1));assert len(rays)==240;values=[];pairs=set()
    for r in rays:
        q=[Q(max(0,min(dot(row,r)for row in A)),2)for A in functions];assert sum(a*b for a,b in zip(q,null))==0;value=sum(a*b for a,b in zip(q,weights));assert value>=0;values.append(value)
        ids=tuple(i for i,v in enumerate(q)if v)
        if ids:assert len(ids)==2 and q[ids[0]]==q[ids[1]] and null[ids[0]]==-null[ids[1]];pairs.add(ids)
    assert len(pairs)==120;assert sorted(j if i==base else i for i,j in pairs if base in(i,j))==sorted(positive)
    assert max(values)>0
    report={'status':'PASS_EXACT_F4_NONNEGATIVE_CONE_COUNTEREXAMPLE','function':'sum of the four dominant transforms and the balanced transform, minus q','positive_functions':positive,'negative_function':base,'positive_frame_rows_twice':[functions[i]for i in positive],'opposite_kernel_zero_coefficient_function':other,'rays':240,'nonzero_ray_pairs':120,'max_ray_value':str(max(values)),'no_nonnegative_coefficient_reason':'The unique global zero relation has coefficient+1 at the negative base term and-1 at a zero coefficient. A nonnegative representative would require its scalar t>=1 and t<=0.','scope':'Nonnegative function in the48-q span with no nonnegative coefficient representative. This alone does not establish a shallow outer-ReLU fold.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path('overnight_fixed_f4_cone_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
