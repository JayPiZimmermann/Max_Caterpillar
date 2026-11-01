"""Mix sign patterns from all label permutations in an enlarged first layer.

Candidate search only. Each group permits arbitrary coefficients within
one prescribed activation pattern on all exact arrangement rays. One
binary activates that group. The common value bound is explicit.
"""
import argparse,hashlib,json,math,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import coo_matrix
from overnight_fixed_fullpair_dictionary import FEATURE,primitive
from overnight_fixed_enlarged_first import rays,network


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--budget',type=int,default=180);ap.add_argument('--bound',type=int,default=8);args=ap.parse_args();start=time.monotonic();prefix='overnight_fixed_enlarged_patterns';known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());new=np.load('overnight_fixed_nonpair_remainder_0_dictionary.npz')['normals'].tolist();first=known['first_layer'][:14]+new;nf=len(first);X=np.asarray(rays(first),dtype=int);Phi=np.maximum(X@np.asarray(first).T,0);V=np.load('overnight_fixed_fullpair_dictionary_0_values.npz')['values'];FF=sp.Matrix(FEATURE.tolist());initial=[];patterns=[];indices={}
    for j,v in enumerate(V):
        w=[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(v.tolist()))[0]]+[Q(0)]*len(new);sgn=tuple(int(np.sign(float(sum(c*int(f)for c,f in zip(w,row)))))for row in Phi)
        if sgn not in indices:indices[sgn]=len(initial);initial.append(w);patterns.append(sgn)
    groups=[(j,sgn)for j in range(len(initial))for sgn in(1,-1)];ng=len(groups);n=nf*(ng+1)+ng;z0=nf*(ng+1);rr=[];cc=[];vv=[];lo=[];hi=[]
    def add(row,l,h):
        r=len(lo);lo.append(l);hi.append(h)
        for i,c in row.items():
            if c:rr.append(r);cc.append(i);vv.append(int(c))
    for q,row in enumerate(Phi):
        eq={i:int(c)for i,c in enumerate(row)if c}
        for k,(p,out)in enumerate(groups):
            if patterns[p][q]>0:
                for f,c in enumerate(row):
                    if c:eq[nf*(k+1)+f]=int(c)*out
        add(eq,int(max(X[q])),int(max(X[q])))
    for k,(p,out)in enumerate(groups):
        for q,row in enumerate(Phi):
            co={nf*(k+1)+f:int(c)*patterns[p][q]for f,c in enumerate(row)if c}
            if patterns[p][q]:
                add(co,0,np.inf);co[z0+k]=-args.bound;add(co,-np.inf,0)
            else:add({nf*(k+1)+f:int(c)for f,c in enumerate(row)if c},0,0)
    add({z0+k:1 for k in range(ng)},-np.inf,3);A=coo_matrix((vv,(rr,cc)),shape=(len(lo),n)).tocsc();lb=np.r_[np.full(z0,-np.inf),np.zeros(ng)];ub=np.r_[np.full(z0,np.inf),np.ones(ng)];integrality=np.r_[np.zeros(z0),np.ones(ng)];objective=np.r_[np.zeros(z0),np.ones(ng)];target=np.asarray(hi)
    # The four old preactivation patterns provide a positive control of
    # both new-feature coefficients and all350-ray sign constraints.
    selected=[]
    for row,out in zip(known['second_layer'][2:],known['output'][2:]):
        w=list(map(Q,row[:14]))+[Q(0)]*len(new);sgn=tuple(int(np.sign(float(sum(c*int(f)for c,f in zip(w,r)))))for r in Phi)
        if sgn not in indices:sgn=tuple(-s for s in sgn)
        selected.append(groups.index((indices[sgn],int(out))))
    cub=ub.copy();clb=lb.copy();cub[z0:]=0
    for k in selected:clb[z0+k]=cub[z0+k]=1
    chi=np.asarray(hi,dtype=float);chi[-1]=4;control=milp(c=objective,integrality=integrality,bounds=Bounds(clb,cub),constraints=LinearConstraint(A,np.asarray(lo),chi),options={'time_limit':20,'disp':False});assert control.x is not None,control.message
    print(json.dumps({'stage':'CONTROL_PASS','patterns':len(initial),'groups':ng,'rays':len(X),'variables':n,'equations_and_inequalities':len(lo),'seconds':time.monotonic()-start}),flush=True)
    r=milp(c=objective,integrality=integrality,bounds=Bounds(lb,ub),constraints=LinearConstraint(A,np.asarray(lo),np.asarray(hi)),options={'time_limit':args.budget,'disp':False});report={'status':'BOUNDED_ENLARGED_PATTERN_SEARCH_INCOMPLETE','solver_status':r.status,'message':r.message,'value_bound':args.bound,'patterns':len(initial),'groups':ng,'rays':len(X),'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if r.x is not None:
        x=[Q(float(c)).limit_denominator(1000000)for c in r.x];take=[k for k in range(ng)if r.x[z0+k]>.5];candidate={'first_layer':first,'remainder':list(map(str,x[:nf])),'outer_forms':[list(map(str,x[nf*(k+1):nf*(k+2)]))for k in take],'output':[str(groups[k][1])for k in take],'initial_forms':[list(map(str,initial[groups[k][0]]))for k in take]};Path(prefix+'_candidate.json').write_text(json.dumps(candidate,indent=2)+'\n');Path(prefix+'_net.json').write_text(json.dumps(network(candidate),indent=2)+'\n');report.update(status='RATIONAL_CANDIDATE_REQUIRES_INDEPENDENT_CHECK',h1=nf+2,h2=len(take)+2)
    Path(prefix+'.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
