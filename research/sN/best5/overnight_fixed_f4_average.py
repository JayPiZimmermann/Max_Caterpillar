"""Exact four-ray test of the fully averaged 48-function F4 orbit."""
from fractions import Fraction as Q
import hashlib,json,math
from pathlib import Path


def primitive(v):
    d=math.gcd(*v)
    assert d
    return tuple(c//d for c in v)


def main():
    data=json.loads(Path('overnight_fixed_f4_inventory.json').read_text())
    rays={tuple(r) for r in data['rays']}; unseen=set(rays); orbits=[]
    while unseen:
        r=min(unseen)
        orbit={primitive(tuple(sum(A[4*i+j]*r[j] for j in range(4)) for i in range(4))) for A in data['group']}
        assert orbit<=rays
        unseen-=orbit;orbits.append((r,orbit))
    assert len(orbits)==4
    rows=[]
    for r,orbit in orbits:
        # Q_i here is the canonical q4, with unit-length frame rows.
        f=sum((Q(max(0,min(sum(a*b for a,b in zip(row,r)) for row in A)),2) for A in data['functions']),Q(0))
        short=long=Q(0)
        for h in data['hyperplanes']:
            value=abs(sum(a*b for a,b in zip(h,r)));norm2=sum(a*a for a in h)
            if norm2==1:short+=value
            elif norm2==4:short+=Q(value,2)
            else:assert norm2==2;long+=value
        rows.append({'ray':r,'orbit_size':len(orbit),'sum_48_q':str(f),'short_absolute_sum':str(short),'long_absolute_sum':str(long)})
    # Solve all four equations by exact elimination, retaining a contradiction.
    matrix=[[Q(row['short_absolute_sum']),Q(row['long_absolute_sum']),Q(row['sum_48_q'])] for row in rows]
    original=[row[:] for row in matrix]; combinations=[[Q(i==j) for j in range(4)] for i in range(4)];rank=0
    for col in range(2):
        pivot=next((i for i in range(rank,4) if matrix[i][col]),None)
        if pivot is None:continue
        matrix[rank],matrix[pivot]=matrix[pivot],matrix[rank];combinations[rank],combinations[pivot]=combinations[pivot],combinations[rank]
        factor=matrix[rank][col];matrix[rank]=[v/factor for v in matrix[rank]];combinations[rank]=[v/factor for v in combinations[rank]]
        for i in range(4):
            if i==rank:continue
            factor=matrix[i][col]
            matrix[i]=[a-factor*b for a,b in zip(matrix[i],matrix[rank])];combinations[i]=[a-factor*b for a,b in zip(combinations[i],combinations[rank])]
        rank+=1
    i=next(i for i in range(4) if not matrix[i][0] and not matrix[i][1] and matrix[i][2])
    multipliers=[v/matrix[i][2] for v in combinations[i]]
    assert [sum(multipliers[i]*original[i][j] for i in range(4)) for j in range(3)]==[0,0,1]
    report={'status':'EXACT_AVERAGED_ORBIT_NOT_SHALLOW_ON_F4_FAN','ray_orbits':rows,'contradiction_multipliers':list(map(str,multipliers)),'scope':'The sum of the48 canonical orbit functions is outside the invariant shallow span. Averaging consequently excludes any nonzero nonnegative linear combination of the48 functions that is shallow. This does not exclude a positive outer-ReLU fold of several functions.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path('overnight_fixed_f4_average.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
