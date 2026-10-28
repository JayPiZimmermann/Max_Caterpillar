"""One joint-flattening test derived from the exact five-input selector identity.

All three preactivations and the remainder are re-solved, while retaining
only the corrected identity's activation pattern. The allowed first walls
contain every zero facet of that pattern. A negative LP result is only a
boundary for this particular first-layer span and pattern.
"""
import hashlib,itertools,json,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from overnight_fixed_fullpair_dictionary import PERMS,primitive
from overnight_fixed_enlarged_first import rays,refine


def values(x):
    a,b,c,d,e=x;m=min(a,b);M=max(a,b);D=max(d,e)
    return(a-max(b,c)+D-m,b-max(a,c)+D-m,max(c,m)-M-D+m)


def main():
    start=time.monotonic();prefix='overnight_fixed_selector_flatten';known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());first14=known['first_layer'][:14];H={tuple(h)for h in np.load('overnight_fixed_nonpair_remainder_0_dictionary.npz')['normals']}
    for p in PERMS:
        rank={i:k for k,i in enumerate(p)};small=lambda i,j:i if rank[i]>rank[j]else j;large=lambda i,j:i if rank[i]<rank[j]else j;m=small(0,1);M=large(0,1);D=large(3,4)
        for terms in(((0,1),(large(1,2),-1),(D,1),(m,-1)),((1,1),(large(0,2),-1),(D,1),(m,-1)),((large(2,m),1),(M,-1),(D,-1),(m,1))):
            g=[0]*5
            for i,c in terms:g[i]+=c
            v=[sum(g[p[i]]for i in range(k))for k in range(1,5)]
            if min(v)<0<max(v):H.add(primitive(g))
    H.difference_update(primitive(a)for a in first14);first=first14+[list(h)for h in sorted(H)];nf=len(first);X=np.asarray(rays(first),dtype=int);Phi=np.maximum(X@np.asarray(first).T,0);G=np.asarray([values(x)for x in X]);E=np.hstack([Phi,Phi*(G[:,0:1]>0),Phi*(G[:,1:2]>0),-Phi*(G[:,2:3]>0)]);b=np.max(X,axis=1);I=[];Z=[]
    for q,row in enumerate(Phi):
        for j in range(3):
            block=[0]*(4*nf);block[nf*(j+1):nf*(j+2)]=list(row)
            if G[q,j]==0:Z.append(block)
            else:I.append([-int(np.sign(G[q,j]))*int(c)for c in block])
    if Z:E=np.r_[E,np.asarray(Z)];b=np.r_[b,np.zeros(len(Z))]
    # The old four-term identity must still be available in this refined fan.
    old=[list(map(Q,row[:14]))+[Q(0)]*(nf-14)for row in known['second_layer'][2:]];control=refine(first,old,list(map(int,known['output'][2:])));assert'candidate'in control
    result=linprog(np.zeros(4*nf),A_eq=E,b_eq=b,A_ub=np.asarray(I),b_ub=np.zeros(len(I)),bounds=[(None,None)]*(4*nf),method='highs');report={'status':'JOINT_SELECTOR_PATTERN_TEST','solver_status':result.status,'message':result.message,'first_features':nf,'rays':len(X),'equations':len(E),'inequalities':len(I),'positive_control':'KNOWN_FOUR_TERM_GLOBAL_PATTERN_PASS','seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if result.x is not None:
        x=[Q(float(c)).limit_denominator(1000000)for c in result.x];assert all(sum(Q(int(c))*v for c,v in zip(row,x))==Q(float(rhs)).limit_denominator(1000000)for row,rhs in zip(E,b));assert all(sum(Q(int(c))*v for c,v in zip(row,x))<=0 for row in I);candidate={'first_layer':first,'remainder':list(map(str,x[:nf])),'outer_forms':[list(map(str,x[nf*(j+1):nf*(j+2)]))for j in range(3)],'output':['1','1','-1'],'initial_pattern':'corrected_selector'};Path(prefix+'_candidate.json').write_text(json.dumps(candidate,indent=2)+'\n');report['status']='RATIONAL_CANDIDATE_REQUIRES_GLOBAL_CHECK'
    Path(prefix+'.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
