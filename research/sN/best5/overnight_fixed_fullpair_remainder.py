"""Permit extra arbitrary first-layer hyperplanes in the linear remainder.

The free outer preactivations remain in the full coordinate-comparison span.
Each possible extra remainder hyperplane is a full input-space extension
of an interior crease in the structured outer dictionary. Thus a candidate
can lower the second width by increasing the first width beyond16.
"""
import argparse,hashlib,json,itertools,math,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import coo_matrix,hstack,eye,vstack,save_npz
from overnight_fixed_fullpair_dictionary import SETS,PERMS,FEATURE,CHAINS,MOBIUS,TARGET,primitive
from overnight_fixed_fullpair_pattern import EDGES


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--tier',type=int,default=0);ap.add_argument('--budget',type=int,default=120);args=ap.parse_args();start=time.monotonic();prefix=f'overnight_fixed_nonpair_remainder_{args.tier}';V=np.load(f'overnight_fixed_fullpair_dictionary_{args.tier}_values.npz')['values'];m=len(V);curves=[];normals=set()
    for perm,ch in zip(PERMS,CHAINS):
        records={}
        for j,v in enumerate(V[:,ch]):
            if min(v)>=0 or max(v)<=0:continue
            grad=[0]*5;prev=0
            for label,value in zip(perm[:-1],v):grad[label]=int(value)-prev;prev=int(value)
            grad[perm[-1]]=-prev;normal=primitive(grad);factor=math.gcd(*grad);records[j]=(normal,factor);normals.add(normal)
        curves.append(records)
    H=sorted(normals);hid={h:i for i,h in enumerate(H)};n=len(H);R=np.asarray([[sum(h[i]for i in range(5)if s>>i&1)for s in SETS]for h in H],dtype=np.int64);rr=[];cc=[];vv=[];nr=0
    for p,ch in enumerate(CHAINS):
        rows={}
        for k,w in enumerate(R[:,ch]):
            if min(w)>=0 or max(w)<=0:continue
            rows[H[k]]=nr;rr.append(nr);cc.append(k);vv.append(1);nr+=1
        for j,(h,factor)in curves[p].items():rr.append(rows[h]);cc.append(n+j);vv.append(factor)
    D=np.maximum(np.r_[R,V],0)@MOBIUS.T
    for j,row in enumerate(D):
        for k,c in enumerate(row):
            if c:rr.append(nr+k);cc.append(j);vv.append(int(c))
    A=coo_matrix((vv,(rr,cc)),shape=(nr+16,n+m),dtype=float).tocsc();b=np.r_[np.zeros(nr),TARGET];np.savez(prefix+'_dictionary.npz',values=V,hyperplanes=R,normals=np.asarray(H));save_npz(prefix+'_matrix.npz',A)
    print(json.dumps({'stage':'MATRIX_READY','outer_forms':m,'extra_first_hyperplanes':n,'equations':len(b),'seconds':time.monotonic()-start}),flush=True)
    # Ordinary exact four-term control is carried along with zero new remainder.
    known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());control=np.zeros(n+m)
    for row,out in zip(known['second_layer'][2:],known['output'][2:]):
        w=list(map(Q,row[:14]));v=[sum(c*int(f)for c,f in zip(w,r))for r in FEATURE];den=math.lcm(*(c.denominator for c in v));iv=[int(c*den)for c in v];pv=primitive(iv);j=next(i for i,r in enumerate(V)if tuple(r)==pv);control[n+j]+=float(Q(out)*Q(math.gcd(*iv),den))
    assert max(abs(A@control-b))==0
    B=8;I=eye(m,format='csc');Z=coo_matrix((m,n));C=hstack([A,coo_matrix((A.shape[0],m))],format='csc');L=hstack([Z,I,-B*I],format='csc');U=hstack([Z,-I,-B*I],format='csc');card=coo_matrix((np.ones(m),(np.zeros(m),np.arange(n+m,n+2*m))),shape=(1,n+2*m)).tocsc();constraints=LinearConstraint(vstack([C,L,U,card],format='csc'),np.r_[b,np.full(2*m+1,-np.inf)],np.r_[b,np.zeros(2*m),3]);r=milp(c=np.r_[np.zeros(n+m),np.ones(m)],integrality=np.r_[np.zeros(n+m),np.ones(m)],bounds=Bounds(np.r_[np.full(n,-np.inf),np.full(m,-B),np.zeros(m)],np.r_[np.full(n,np.inf),np.full(m,B),np.ones(m)]),constraints=constraints,options={'time_limit':args.budget,'disp':False});report={'status':'EXTRA_FIRST_HYPERPLANE_SEARCH_INCOMPLETE','solver_status':r.status,'message':r.message,'outer_forms':m,'extra_first_hyperplanes':n,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if r.x is not None:
        extra=[Q(float(c)).limit_denominator(1000000)for c in r.x[:n]];take=np.flatnonzero(abs(r.x[n:n+m])>1e-8);DD=[Q(float(r.x[n+j])).limit_denominator(1000000)for j in take];FF=sp.Matrix(FEATURE.tolist());WW=[[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(V[j].tolist()))[0]]for j in take];target=[Q(1-int(s&1))-sum(d*max(Q(int(V[j,q])),Q(0))for d,j in zip(DD,take))-sum(d*max(int(R[k,q]),0)for k,d in enumerate(extra))for q,s in enumerate(SETS)];remainder=[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(target))[0]];active=[i for i,c in enumerate(extra)if c];first=[]
        for i,j in EDGES:a=[0]*5;a[i]=1;a[j]=-1;first.append(a)
        first.extend(H[i]for i in active);first.extend([[1,0,0,0,0],[-1,0,0,0,0]]);head=remainder+[extra[i]for i in active];second=[list(map(str,head))+['1','-1'],list(map(str,[-c for c in head]))+['-1','1']];second.extend(list(map(str,w))+['0']*(len(active)+2)for w in WW);net={'N':5,'first_layer':first,'second_layer':second,'output':['1','-1']+list(map(str,DD))};Path(prefix+'_candidate_net.json').write_text(json.dumps(net,indent=2)+'\n');report.update(status='RATIONAL_CANDIDATE_REQUIRES_INDEPENDENT_CHECK',h1=len(first),h2=len(second),new_hyperplanes=len(active))
    Path(prefix+'.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
