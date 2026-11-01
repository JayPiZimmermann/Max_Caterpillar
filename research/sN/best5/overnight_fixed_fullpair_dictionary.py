"""Structured full-pair dictionary: exact global rows, no sample fitting.

Candidate forms are S5 images of small linear combinations of the four
preactivations in the known exact identity. Finite dictionary sparsity
bounds are only diagnostics. A successful rational candidate must pass
the independent input-gradient checker.
"""
import argparse,hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import coo_matrix,hstack,eye,load_npz,save_npz
from overnight_fixed_fullpair_pattern import EDGES,network
from overnight_fixed_cross_verify import check

SETS=[sum(1<<i for i in c)for n in range(1,5)for c in itertools.combinations(range(5),n)]
SID={s:i for i,s in enumerate(SETS)}
PERMS=list(itertools.permutations(range(5)))
FEATURE=np.asarray([[int(bool(s>>i&1)and not bool(s>>j&1))for i,j in EDGES]for s in SETS],dtype=np.int64)
CHAINS=[[SID[sum(1<<i for i in p[:k])]for k in range(1,5)]for p in PERMS]
MOBIUS=np.asarray([[(-1)**(s.bit_count()-t.bit_count())if t&s==t else 0 for t in SETS]for s in range(32)if s.bit_count()>=3],dtype=np.int64)
TARGET=np.asarray([(-1)**(s.bit_count()+1)for s in range(32)if s.bit_count()>=3])


def primitive(v):
    d=math.gcd(*map(int,v))
    if not d:return None
    if next(int(c)for c in v if c)<0:d=-d
    return tuple(int(c)//d for c in v)


def make(tier):
    known=json.loads(Path("overnight_fixed_fullpair_pattern_control_net.json").read_text())
    seeds=[]
    for row in known['second_layer'][2:]:
        w=list(map(Q,row[:14]));v=[sum(c*int(f)for c,f in zip(w,r))for r in FEATURE];den=math.lcm(*(x.denominator for x in v));seeds.append(np.asarray([int(x*den)for x in v]))
    base={primitive(v)for v in seeds}
    if tier>=1:
        base.update(primitive(sum((c*v for c,v in zip(co,seeds)),np.zeros(30,dtype=np.int64)))for co in itertools.product((-1,0,1),repeat=4))
    base.discard(None);allforms=set()
    for p in PERMS:
        ix=[SID[sum(1<<p[i]for i in range(5)if s>>i&1)]for s in SETS]
        allforms.update(primitive([v[i]for i in ix])for v in base)
    V=np.asarray(sorted(allforms),dtype=np.int64)
    rows=[];cols=[];values=[];nr=0
    for chain in CHAINS:
        normals={}
        for j,v in enumerate(V[:,chain]):
            if min(v)>=0 or max(v)<=0:continue
            normal=primitive(v);factor=math.gcd(*map(int,v))
            if normal not in normals:normals[normal]=nr;nr+=1
            rows.append(normals[normal]);cols.append(j);values.append(factor)
    D=np.maximum(V,0)@MOBIUS.T
    for j,v in enumerate(D):
        for k,c in enumerate(v):
            if c:rows.append(nr+k);cols.append(j);values.append(int(c))
    A=coo_matrix((values,(rows,cols)),shape=(nr+16,len(V)),dtype=float).tocsc();b=np.r_[np.zeros(nr),TARGET]
    return V,A,b


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--tier',type=int,default=0);ap.add_argument('--budget',type=int,default=240);ap.add_argument('--bound',type=int,default=8);args=ap.parse_args();start=time.monotonic();prefix=f'overnight_fixed_fullpair_dictionary_{args.tier}'
    V,A,b=make(args.tier);m=len(V);np.savez(prefix+'_values.npz',values=V);save_npz(prefix+'_matrix.npz',A)
    print(json.dumps({'stage':'MATRIX_READY','forms':m,'equations':len(b),'nonzero':A.nnz,'seconds':time.monotonic()-start}),flush=True)
    # Global relation quotient and interior curvature vanish exactly on the known identity.
    known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());d=np.zeros(m)
    for row,out in zip(known['second_layer'][2:],known['output'][2:]):
        w=list(map(Q,row[:14]));v=[sum(c*int(f)for c,f in zip(w,r))for r in FEATURE];den=math.lcm(*(x.denominator for x in v));iv=[int(x*den)for x in v];p=primitive(iv);g=math.gcd(*iv);d[next(j for j,r in enumerate(V)if tuple(r)==p)]+=float(Q(out)*Q(g,den))
    assert np.max(abs(A@d-b))==0
    # A single binary records either output sign; the coefficient bound is explicit.
    eyeM=eye(m,format='csc');B=args.bound
    C=hstack([A,coo_matrix((A.shape[0],m))],format='csc')
    L=hstack([eyeM,-B*eyeM],format='csc');U=hstack([-eyeM,-B*eyeM],format='csc')
    C3=coo_matrix((np.ones(m),(np.zeros(m),np.arange(m,2*m))),shape=(1,2*m)).tocsc()
    from scipy.sparse import vstack
    constraints=LinearConstraint(vstack([C,L,U,C3],format='csc'),np.r_[b,np.full(2*m+1,-np.inf)],np.r_[b,np.zeros(2*m),3])
    r=milp(c=np.r_[np.zeros(m),np.ones(m)],integrality=np.r_[np.zeros(m),np.ones(m)],bounds=Bounds(np.r_[np.full(m,-B),np.zeros(m)],np.r_[np.full(m,B),np.ones(m)]),constraints=constraints,options={'time_limit':args.budget,'disp':False})
    report={'status':'FINITE_DICTIONARY_SEARCH','solver_status':r.status,'message':r.message,'tier':args.tier,'forms':m,'equations':len(b),'output_bound':B,'seconds':time.monotonic()-start,'positive_control':'KNOWN_FOUR_TERM_IDENTITY_EXACT_ROW_PASS','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if r.x is not None:
        support=np.flatnonzero(abs(r.x[:m])>1e-8);DD=[Q(float(r.x[j])).limit_denominator(1000000)for j in support];report['support']=len(support)
        import sympy as sp
        FF=sp.Matrix(FEATURE.tolist());WW=[]
        for j in support:WW.append([Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(V[j].tolist()))[0]])
        target=[Q(1-int(s&1))-sum(d*max(Q(int(V[j,q])),Q(0))for d,j in zip(DD,support))for q,s in enumerate(SETS)]
        R=[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(target))[0]]
        cand={'remainder':list(map(str,R)),'outer_forms':[list(map(str,w))for w in WW],'output':list(map(str,DD))}
        path=Path(prefix+'_net.json');path.write_text(json.dumps(network(cand),indent=2)+'\n');receipt=check(path);Path(prefix+'_check.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');report['status']='EXACT_MATCHED_SIXTEEN_FIVE_CONSTRUCTION'
    Path(prefix+'.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
