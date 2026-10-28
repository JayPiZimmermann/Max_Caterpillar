"""Full-pair construction dictionary using sparse top-tie ray values.

These are structured candidates, not an exhaustive real-parameter domain.
Every proposed identity is checked by exact input-gradient cancellation.
"""
import argparse,hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import coo_matrix,hstack,eye,vstack,save_npz
from overnight_fixed_fullpair_dictionary import SETS,SID,PERMS,FEATURE,CHAINS,MOBIUS,TARGET,primitive
from overnight_fixed_fullpair_pattern import network
from overnight_fixed_cross_verify import check


def generate(support,bound):
    ids=[i for i,s in enumerate(SETS)if s.bit_count()>=3];top=FEATURE[ids];F=sp.Matrix(top.tolist());relation=[1 if SETS[i].bit_count()==3 else -3 for i in ids]
    # The last row is omitted; any14 of15 rows are independent.
    inverse=sp.Matrix(F[:14,:]).inv();transfer=sp.Matrix(FEATURE.tolist())*inverse
    base=set()
    for positions in itertools.combinations(range(15),support):
        last=positions[-1]
        for raw in itertools.product(range(-bound,bound+1),repeat=support-1):
            if not all(raw)or raw[0]<0:continue
            tail=-sum(relation[i]*v for i,v in zip(positions,raw))
            if tail%relation[last]:continue
            tail//=relation[last]
            if not tail or abs(tail)>3*bound:continue
            vv=[0]*15
            for i,v in zip(positions,raw+(tail,)):vv[i]=v
            v=transfer*sp.Matrix(vv[:14]);den=sp.ilcm(*(c.q for c in v));base.add(primitive([int(c*den)for c in v]))
    return base


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--support',type=int,default=3);ap.add_argument('--bound',type=int,default=1);ap.add_argument('--budget',type=int,default=240);args=ap.parse_args();start=time.monotonic();prefix=f'overnight_fixed_fullpair_sparse{args.support}_{args.bound}'
    base=set()
    for s in range(2,args.support+1):base.update(generate(s,args.bound))
    # Include the exact four-neuron control, independently of this family.
    known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text())
    for row in known['second_layer'][2:]:
        w=list(map(Q,row[:14]));v=[sum(c*int(f)for c,f in zip(w,r))for r in FEATURE];den=math.lcm(*(c.denominator for c in v));base.add(primitive([int(c*den)for c in v]))
    V=np.asarray(sorted(base),dtype=np.int64);m=len(V);rows=[];cols=[];vals=[];nr=0
    for ch in CHAINS:
        groups={}
        for j,v in enumerate(V[:,ch]):
            if min(v)>=0 or max(v)<=0:continue
            key=primitive(v)
            if key not in groups:groups[key]=nr;nr+=1
            rows.append(groups[key]);cols.append(j);vals.append(math.gcd(*map(int,v)))
    D=np.maximum(V,0)@MOBIUS.T
    for j,v in enumerate(D):
        for i,c in enumerate(v):
            if c:rows.append(nr+i);cols.append(j);vals.append(int(c))
    A=coo_matrix((vals,(rows,cols)),shape=(nr+16,m),dtype=float).tocsc();b=np.r_[np.zeros(nr),TARGET];np.savez(prefix+'_values.npz',values=V);save_npz(prefix+'_matrix.npz',A)
    print(json.dumps({'stage':'MATRIX_READY','forms':m,'equations':len(b),'seconds':time.monotonic()-start}),flush=True)
    control=np.zeros(m)
    for row,out in zip(known['second_layer'][2:],known['output'][2:]):
        w=list(map(Q,row[:14]));v=[sum(c*int(f)for c,f in zip(w,r))for r in FEATURE];den=math.lcm(*(c.denominator for c in v));iv=[int(c*den)for c in v];p=primitive(iv);control[next(i for i,r in enumerate(V)if tuple(r)==p)]+=float(Q(out)*Q(math.gcd(*iv),den))
    assert np.max(abs(A@control-b))==0
    B=8;I=eye(m,format='csc');C=hstack([A,coo_matrix(A.shape)],format='csc');P=hstack([I,-B*I],format='csc');M=hstack([-I,-B*I],format='csc');card=coo_matrix((np.ones(m),(np.zeros(m),np.arange(m,2*m))),shape=(1,2*m)).tocsc()
    constraint=LinearConstraint(vstack([C,P,M,card],format='csc'),np.r_[b,np.full(2*m+1,-np.inf)],np.r_[b,np.zeros(2*m),3]);r=milp(c=np.r_[np.zeros(m),np.ones(m)],integrality=np.r_[np.zeros(m),np.ones(m)],bounds=Bounds(np.r_[np.full(m,-B),np.zeros(m)],np.r_[np.full(m,B),np.ones(m)]),constraints=constraint,options={'time_limit':args.budget,'disp':False})
    report={'status':'FINITE_SPARSE_RAY_DICTIONARY_SEARCH','solver_status':r.status,'message':r.message,'support':args.support,'bound':args.bound,'output_bound':B,'forms':m,'equations':len(b),'seconds':time.monotonic()-start,'positive_control':'KNOWN_FOUR_TERM_IDENTITY_EXACT_ROW_PASS','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if r.x is not None:
        take=np.flatnonzero(abs(r.x[:m])>1e-8);DD=[Q(float(r.x[j])).limit_denominator(1000000)for j in take];report['free_width']=len(take);FF=sp.Matrix(FEATURE.tolist());WW=[[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(V[j].tolist()))[0]]for j in take];target=[Q(1-int(s&1))-sum(d*max(Q(int(V[j,q])),Q(0))for d,j in zip(DD,take))for q,s in enumerate(SETS)];R=[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(target))[0]];cand={'remainder':list(map(str,R)),'outer_forms':[list(map(str,w))for w in WW],'output':list(map(str,DD))};path=Path(prefix+'_net.json');path.write_text(json.dumps(network(cand),indent=2)+'\n');receipt=check(path);Path(prefix+'_check.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');report['status']='EXACT_MATCHED_SIXTEEN_FIVE_CONSTRUCTION'
    Path(prefix+'.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
