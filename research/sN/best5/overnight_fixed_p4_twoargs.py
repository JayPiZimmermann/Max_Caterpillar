"""Small continuous-coefficient proposal search for a four-free-term P4 identity.
Two comparison forms vary independently; the symmetric two terms stay fixed.
Any candidate requires the separate exact global checker. Negative MIP status
has only the explicitly bounded scope stated in the report.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib,json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix


def main():
    started=time.monotonic();records={}
    for p in product(range(-2,3),repeat=4):
        u,v,s,t=p;a,b,c,d=[max(x,0)for x in p];z=(a,b,max(v-u,0),c,d,max(s-t,0),max(v-t,0));target=Q(2*max(a,b,c,d)-(a+b+max(abs(a-b),abs(c-d))),2)
        if z in records:assert records[z]==target
        records[z]=target
    Z=np.array(list(records),dtype=float);target=np.array([float(v)for v in records.values()]);n=len(Z);nv=14+4*n;entries=[];lo=[];hi=[]
    def row(coef,l,h):
        k=len(lo);entries.extend((k,j,float(v))for j,v in coef.items()if v);lo.append(l);hi.append(h)
    cap=16
    for i,z in enumerate(Z):
        M=max(1,cap*sum(z));row({14+i:1,14+n+i:-1},target[i],target[i])
        for k in range(2):
            y=14+k*n+i;b=14+2*n+k*n+i;lin={7*k+j:-v for j,v in enumerate(z)if v};lin[y]=1;row(lin,0,np.inf);lin2=dict(lin);lin2[b]=M;row(lin2,-np.inf,M);row({y:1,b:-M},-np.inf,0)
    ii,jj,vv=zip(*entries);A=coo_matrix((vv,(ii,jj)),shape=(len(lo),nv)).tocsc();bounds=Bounds(np.r_[np.full(14,-cap),np.zeros(4*n)],np.r_[np.full(14,cap),np.full(2*n,np.inf),np.ones(2*n)]);integrality=np.r_[np.zeros(14+2*n),np.ones(2*n)];objective=np.zeros(nv)
    r=milp(objective,integrality=integrality,bounds=bounds,constraints=LinearConstraint(A,np.array(lo),np.array(hi)),options={'time_limit':50,'mip_rel_gap':0})
    report={'status':'BOUNDED_CONTINUOUS_TWO_ARGUMENT_DIAGNOSTIC','solver_status':r.status,'message':r.message,'feature_points':n,'coefficient_bound':cap,'seconds':time.monotonic()-started,'scope':'Only the family with two fixed symmetric half-weight terms and two freely varied comparison forms; unsuccessful bounded search is not a mathematical exclusion.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if r.x is not None:
        L=[Q(float(v)).limit_denominator(1000000)for v in r.x[:7]];M=[Q(float(v)).limit_denominator(1000000)for v in r.x[7:14]];errors=[]
        for z,t in records.items():
            actual=max(sum(c*v for c,v in zip(L,z)),Q(0))-max(sum(c*v for c,v in zip(M,z)),Q(0))
            if actual!=t:errors.append(z)
        report.update(L=list(map(str,L)),M=list(map(str,M)),exact_sample_errors=len(errors))
        if not errors:
            old=json.loads(Path('research/sN/best5/overnight_fixed_cross_net9_14_simple.json').read_text());R=[1,0,0,0,0,0,0,1,-1];net={'N':5,'first_layer':old['first_layer'],'second_layer':[R,[-v for v in R],list(map(str,L))+[0,0],list(map(str,M))+[0,0],[-1,1,0,-1,1,0,0,0,0],[-1,1,0,1,-1,0,0,0,0]],'output':[1,-1,1,-1,'1/2','1/2']};Path('research/sN/best5/overnight_fixed_p4_twoargs_candidate.json').write_text(json.dumps(net,indent=2)+'\n');report['status']='EXACT_SAMPLE_CANDIDATE_REQUIRES_GLOBAL_GATE'
    Path('research/sN/best5/overnight_fixed_p4_twoargs.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2),flush=True)
if __name__=='__main__':main()
