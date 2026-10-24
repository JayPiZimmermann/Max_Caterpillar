"""Exact controls for the clean S=0, z=2 eta_i pendant-pair residue.

Generic eta obey sum eta=0, with no additional subset-sum/ratio coincidence.
The selected eta_i is1; powers5 prevent unintended cuts of sum±2 or±4.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,time
from dfs_review_fourier import family
from overnight_uniform_pruning_residue_recurrence import adj,normalized,smaller,rooted_kernel

def direct(unit,eta,index=0):
    n=len(eta)+2;labels=[0]+sorted(adj(unit));constant=[0,0]+list(eta);zcoeff=[1,-1]+[0]*len(eta);scoeff=[0,-1]+[0]*(len(eta)-1)+[1];z0=2*eta[index];factors=normalized(unit);total=Q(0);hits=0
    for p in itertools.permutations(range(n)):
        b=dict(zip(labels,[constant[i]for i in p]));c=dict(zip(labels,[zcoeff[i]for i in p]));d=dict(zip(labels,[scoeff[i]for i in p]));den=1;spoles=[];zpoles=[]
        for C,H in factors:
            q=sum(b[v]for v in C);t=sum(c[v]for v in C);s=sum(d[v]for v in C)
            for off in(H,H+1):
                q0=q+off*b[0];t0=t+off*c[0];s0=s+off*d[0]
                if q0==0 and t0==0:assert s0;spoles.append(s0)
                elif q0+z0*t0==0:assert t0;zpoles.append(t0)
                else:den*=q0+z0*t0
        assert len(spoles)<=1
        if spoles:
            assert len(zpoles)<=1
            if zpoles:
                a=b[0]+z0*c[0];total+=Q((-a)**(n-4),den*spoles[0]*zpoles[0]);hits+=1
    return total,hits

def predicted(unit,eta,index=0):
    A=adj(unit);r=unit['root'];E=set(map(tuple,unit['edges']))
    if len(A[r])!=1:return Q(0),None
    h=next(iter(A[r]))
    if(r,h)not in E or len(A[h])!=2:return Q(0),None
    v=next(x for x in A[h]if x!=r)
    if(v,h)not in E:return Q(0),None
    U=smaller(unit,{r,h},v);V=sorted(adj(U));rest=eta[:index]+eta[index+1:];a=eta[index]
    value=-sum(rooted_kernel(U,dict([(0,a)]+list(zip(V,p))))for p in itertools.permutations(rest))
    return value,{'deleted_pair':[r,h],'new_root':v,'lower_unit':U}

def main():
    start=time.monotonic();units=[(u,5)for u in family(5,'all')]
    units.extend(({'root':1,'edges':E},7)for E in [[(1,2),(3,2),(3,4),(4,5),(5,6)],[(2,1),(3,2),(3,4),(4,5),(5,6)],[(1,2),(2,3),(3,4),(4,5),(5,6)]])
    units.append(({'root':5,'edges':[(1,2),(1,3),(3,4),(5,4),(1,6),(6,7),(7,8)]},9))
    rows=[]
    for u,n in units:
        pos=[5**i for i in range(n-3)];eta=pos+[-sum(pos)];lhs,hits=direct(u,eta);rhs,description=predicted(u,eta);assert lhs==rhs,(u,lhs,rhs);rows.append({'arity':n,'unit':{k:v for k,v in u.items()if k!='cuts'},'eta':eta,'value':str(lhs),'double_pole_summands':hits,'pruning':description})
    result={'status':'EXACT_CLEAN_PENDANT_PAIR_DOUBLE_RESIDUE_CONTROLS_PASS','cases':rows,'seconds':time.monotonic()-start,'scope':'The residue is identically zero unless the head root begins a pendant two-edge path with relative signs(-,+); then it is minus the fixed-apex lower kernel sum after deleting the first pair. The maximum maps to zero, so this alone is not a separator.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(rows),result['seconds'],flush=True)
if __name__=='__main__':main()
