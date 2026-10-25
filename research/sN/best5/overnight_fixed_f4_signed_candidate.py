"""Exact cone-saturation counterexample and a small one-fold feasibility test."""
from fractions import Fraction as Q
import hashlib,json,math,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def main():
    start=time.monotonic();data=json.loads(Path('overnight_fixed_f4_inventory.json').read_text());S=json.loads(Path('overnight_fixed_f4_signed_check.json').read_text());R=np.array(data['rays'],dtype=int);H=np.array(data['hyperplanes'],dtype=int);P=np.c_[R,abs(R@H.T)];V=np.array([np.maximum((R@np.array(A).T).min(axis=1),0)for A in data['functions']],dtype=int).T;base=data['base_function'];kernel=np.array(S['relations'][0])-np.array(S['relations'][1])+np.array(S['relations'][2]);assert set(kernel)=={-1,1};assert not np.any(V@kernel)
    edges=set()
    for row in V:
        ids=tuple(np.flatnonzero(row))
        if not ids:continue
        assert len(ids)==2 and row[ids[0]]==row[ids[1]] and kernel[ids[0]]==-kernel[ids[1]];edges.add(ids)
    neighbors=sorted(j if i==base else i for i,j in edges if base in(i,j));weights=np.zeros(48,dtype=int);weights[base]=-1;weights[neighbors]=1;target=V@weights;assert np.all(target>=0);opposite_zero=next(i for i in range(48)if kernel[i]==-kernel[base] and weights[i]==0)
    # The fundamental chamber has these four rays; all group images give its fan.
    fundamental=[(1,0,0,0),(1,1,0,0),(2,1,1,0),(3,1,1,1)];index={tuple(r):i for i,r in enumerate(R)};chambers=set()
    for A in data['group']:
        rays=[]
        for r in fundamental:
            v=tuple(sum(A[4*i+j]*r[j]for j in range(4))for i in range(4));d=math.gcd(*v);rays.append(index[tuple(x//d for x in v)])
        chambers.add(tuple(sorted(rays)))
    assert len(chambers)==1152
    inside=set(i for chamber in chambers if any(target[j]>0 for j in chamber)for i in chamber);inside=sorted(inside);outside=sorted(set(range(240))-set(inside));r=linprog(np.zeros(28),A_eq=P[inside],b_eq=target[inside],A_ub=P[outside]if outside else None,b_ub=np.zeros(len(outside))if outside else None,bounds=[(None,None)]*28,method='highs')
    report={'status':'EXACT_NONNEGATIVE_CONE_NOT_SATURATED','ray_count':240,'nonzero_ray_edge_count':len(edges),'base_function':base,'positive_functions':list(map(int,neighbors)),'negative_functions':[base],'impossible_nonnegative_pair':[base,opposite_zero],'kernel_signs':[int(kernel[base]),int(kernel[opposite_zero])],'pointwise_ray_min':int(min(target)),'pointwise_ray_max':int(max(target)),'chambers':1152,'closure_rays_for_fold':len(inside),'single_fold_solver_status':r.status,'single_fold_message':r.message}
    if r.x is not None:
        coeff=[Q(float(v)).limit_denominator(1000000)for v in r.x];assert all(max(sum(c*int(v)for c,v in zip(coeff,row)),Q(0))==int(t)for row,t in zip(P,target));assert all(sum(c*int(v)for c,v in zip(coeff,P[i]))==int(target[i])for i in inside);report['status']='EXACT_SIGNED_NONNEGATIVE_SINGLE_FOLD';report['shallow_coefficients']=list(map(str,coeff))
    else:
        # Here feasibility fails already on the exact active-cone equalities.
        E=P[inside];b=target[inside];dual=linprog(np.ones(2*len(E)),A_eq=np.r_[np.c_[E.T,-E.T],np.r_[b,-b][None,:]],b_eq=np.r_[np.zeros(28),1],bounds=(0,None),method='highs')
        if dual.success:
            y=[Q(float(dual.x[i]-dual.x[len(E)+i])).limit_denominator(1000000)for i in range(len(E))];assert all(sum(y[i]*int(E[i,j])for i in range(len(E)))==0 for j in range(28));assert sum(y[i]*int(b[i])for i in range(len(E)))==1;report['exact_fold_equality_contradiction']=[[inside[i],str(v)]for i,v in enumerate(y)if v]
    report.update(seconds=time.monotonic()-start,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());Path('overnight_fixed_f4_signed_candidate.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
