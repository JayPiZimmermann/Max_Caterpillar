"""Bounded proposal search for a fold using at most six F4 orbit copies.

Only an independently rational-checked successful candidate is a theorem.
An unsuccessful bounded/time-limited MIP is diagnostic.
"""
import hashlib,json,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix


def main():
    started=time.monotonic();data=json.loads(Path('overnight_fixed_f4_inventory.json').read_text());R=np.array(data['rays'],dtype=int);H=np.array(data['hyperplanes'],dtype=int);P=np.c_[R,abs(R@H.T)];F=data['functions'];base=data['base_function'];vals=[];closed=[]
    for A in F:
        v=R@np.array(A,dtype=int).T;vals.append(np.maximum(v.min(axis=1),0));closed.append(v.min(axis=1)>=0)
    V=np.array(vals,dtype=int).T;C=np.array(closed,dtype=bool).T;n=28+48+48;entries=[];lo=[];hi=[]
    def row(coeff,low,high):
        k=len(lo);entries.extend((k,j,float(c)) for j,c in coeff.items() if c);lo.append(low);hi.append(high)
    for k in range(240):
        coeff={j:int(v) for j,v in enumerate(P[k]) if v};coeff.update({28+j:-int(v) for j,v in enumerate(V[k]) if v});row(coeff,-np.inf,0)
        row({j:int(v) for j,v in enumerate(P[k]) if v},-200,np.inf)
        M=200+20*sum(V[k])
        for i in np.flatnonzero(C[k]):
            d={j:-v for j,v in coeff.items()};d[76+int(i)]=M;row(d,-np.inf,M)
    for i in range(48):row({28+i:1,76+i:-20},-np.inf,0)
    row({76+i:1 for i in range(48)},-np.inf,6)
    ii,jj,vv=zip(*entries);A=coo_matrix((vv,(ii,jj)),shape=(len(lo),n)).tocsc();lower=np.r_[np.full(28,-np.inf),np.zeros(96)];upper=np.r_[np.full(28,np.inf),np.full(48,20),np.ones(48)];lower[28+base]=upper[28+base]=1;lower[76+base]=upper[76+base]=1;integrality=np.r_[np.zeros(76),np.ones(48)];objective=np.r_[np.zeros(76),np.ones(48)]
    r=milp(objective,integrality=integrality,bounds=Bounds(lower,upper),constraints=LinearConstraint(A,np.array(lo),np.array(hi)),options={'time_limit':50,'mip_rel_gap':0,'presolve':True})
    report={'status':'BOUNDED_SMALL_FOLD_DIAGNOSTIC','solver_status':r.status,'message':r.message,'seconds':time.monotonic()-started,'variables':n,'constraints':len(lo),'bounds':{'max_selected_copies':6,'max_weight':20,'min_preactivation_on_rays':-200},'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if r.x is not None:
        x=[Q(float(v)).limit_denominator(1000000) for v in r.x[:76]];weights=x[28:];ids=[i for i,w in enumerate(weights) if w]
        errors=[]
        for k,p in enumerate(P):
            g=sum(a*int(b) for a,b in zip(x[:28],p));target=sum(weights[i]*int(V[k,i]) for i in ids)
            if max(g,Q(0))!=target or (any(C[k,i] for i in ids) and g!=target):errors.append(k)
        report.update(selected_functions=ids,weights=[str(weights[i]) for i in ids],shallow_coefficients=list(map(str,x[:28])),rational_ray_errors=errors)
        if not errors and all(weights[i]>0 for i in ids):report['status']='EXACT_SMALL_POSITIVE_FOLD'
    Path('overnight_fixed_f4_smallfold.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2),flush=True)
if __name__=='__main__':main()
