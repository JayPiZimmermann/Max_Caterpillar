"""Exact controls for the full-corner curvature-score obstruction.

The uniform theorem is analytic; these checks verify normalization,
closed sign boundaries, and compatibility with the old ray-plane control.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json


def pair_score(x,y):return int(x>=0)-int(y>=1)
def score(row,weight=Q(1)):
    row=list(map(Q,row));weight=Q(weight);B,E=row[1],row[4]
    if not B or B+E:return [Q(0)]*4
    if B<0:row=[-x for x in row];B=-B
    alpha,gamma,beta,phi=(row[i]/B for i in(0,2,3,5))
    return [weight*B*pair_score(x,y)for x,y in((alpha,beta),(alpha,phi),(gamma,beta),(gamma,phi))]
def mixed(v):return v[0]-v[1]-v[2]+v[3]
def add(a,b):return [x+y for x,y in zip(a,b)]
def old_to_new(row):return [row[1],row[0],row[2],row[4],row[3],row[5]]


def main():
    # Every normalized corner has ray coefficients x,x+1,y,y-1.
    grid=[Q(-2),Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1),Q(2)];count=0
    for x,y in product(grid,repeat=2):
        ray=(x,x+1,y,y-1);fixed=all(v>=0 for v in ray)or all(v<=0 for v in ray)
        region=(x>=0 and y>=1)or(x<=-1 and y<=0)
        assert fixed==region
        if fixed:assert pair_score(x,y)==0
        else:assert min(ray)<0<max(ray)
        count+=1
    unit_count=0
    for alpha,gamma,beta,phi in product(grid,repeat=4):
        row=[alpha,1,gamma,beta,-1,phi]
        for scale in(Q(-2),Q(-1,2),Q(1,3),Q(3)):
            v=score([scale*x for x in row],Q(-3,2));assert mixed(v)==0
            assert v==score(row,Q(-3,2)*abs(scale));unit_count+=1
    assert score([0,1,0,0,-1,0])==[1,1,1,1]
    # Full target crease on each corner, in that corner's global lift.
    target_normals=([1,0,0,-1,0,0],[1,0,0,0,-1,0],[0,1,0,-1,0,0],[0,1,0,0,-1,0])
    target=[score(row)[i]for i,row in enumerate(target_normals)]
    assert target==[0,0,0,1] and mixed(target)==1
    old=json.loads(Path('research/sN/best5/overnight_fixed_rayplane_control_net.json').read_text());boundary=[Q(0)]*4
    for row,weight in zip(old['second_layer'][2:],old['output'][2:]):boundary=add(boundary,score(old_to_new(row[:6]),Q(weight)))
    assert mixed(boundary)==0
    # Q=P(0)-P(b)-P(-d)+P(b-d), in the old feature convention.
    h1=(-1,1,1,0,0,0);h2=(0,0,0,-1,1,1);terms=[]
    for g,c in[((0,0,0,0,0,0),1),((0,1,0,0,0,0),-1),((0,0,0,0,-1,0),-1),((0,1,0,0,-1,0),1)]:
        terms.extend([(g,-c),(tuple(x-y for x,y in zip(g,h1)),c),(tuple(x+y for x,y in zip(g,h2)),c),(tuple(x-y+z for x,y,z in zip(g,h1,h2)),-c)])
    localized=[Q(0)]*4
    for row,c in terms:localized=add(localized,score(old_to_new(row),Q(c)))
    assert localized==[0,0,0,0]
    report={'status':'PASS_EXACT_FULL_CORNER_SCORE_CONTROLS','sign_boundary_controls':count,'scaled_unit_controls':unit_count,'target_scores':list(map(str,target)),'target_mixed_score':1,'old_rayplane_control_scores':list(map(str,boundary)),'localized_overlap_Q_scores':list(map(str,localized)),'scope':'Exact controls of the analytic all-finite-width obstruction; not a finite enumeration of possible networks.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'old_control_sha256':hashlib.sha256(Path('research/sN/best5/overnight_fixed_rayplane_control_net.json').read_bytes()).hexdigest()}
    p=Path('research/sN/best5/overnight_fixed_natural8_allwidth_score.json');p.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
