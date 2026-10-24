#!/usr/bin/env python3
"""Construct and certify a noncrossing top-class identity at a fixed arity.

Use the dihedral symmetry of the fixed cyclic label order. Modular equations
only propose rational coefficients; complete subspace flags certify the
candidate. A positive result is a finite top-quotient identity, not a
uniform exponential construction or a complete exact network.
"""
import sys,json,time,math
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import numpy as np
from complete_flags import pyramid,simplex,sub

def key(u,n,perm=None):
    if perm is None:perm=list(range(n))
    a=perm[u['apex']];r=perm[u['root']];h=[0]*n;h[r]=1;h[a]=-1;es=[]
    for s,t in u['edges']:
        x,y=perm[s],perm[t]
        if x>y:h[x]+=1;h[y]-=1
        es.append(tuple(sorted((x,y))))
    return tuple(h),tuple(sorted(es))

def ratrec(a,p):
    r0,r1=p,int(a);t0,t1=0,1;lim=math.isqrt(p//2)
    while abs(r1)>lim:
        q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
    if not t1 or abs(t1)>lim:return None
    f=Fraction(r1,t1)
    return f if (f.numerator-a*f.denominator)%p==0 else None

def main():
    n=int(sys.argv[1]);here=Path(__file__).parent;start=time.time()
    D=json.loads((here/f'upper_fourier_{n}_nc.json').read_text());units=D['units'];p=D['prime']
    index={key(u,n):i for i,u in enumerate(units)};seen=set();orbits=[]
    for i,u in enumerate(units):
        if i in seen:continue
        orb={index[key(u,n,[(sg*j+a)%n for j in range(n)])] for sg in (-1,1) for a in range(n)}
        seen|=orb;orbits.append(sorted(orb))
    raw=np.array(D['rows'],dtype=np.int64);A=np.column_stack([raw[:,o].sum(axis=1)%p for o in orbits]+[raw[:,-1]])
    basis={}
    for row in A:
        v=row.copy()
        for j,b in sorted(basis.items()):v=(v-v[j]*b)%p
        nz=np.flatnonzero(v)
        if len(nz):
            j=int(nz[0]);basis[j]=v*pow(int(v[j]),p-2,p)%p
    m=len(orbits);print('orbits',m,'rank',len(basis),flush=True)
    if m in basis:print('MODULAR OBSTRUCTION',flush=True);return
    x=np.zeros(m+1,dtype=np.int64);x[-1]=-1
    for j,b in sorted(basis.items(),reverse=True):x[j]=-int(b@x)%p
    coeff=[ratrec(a,p) for a in x[:-1]]
    print('reconstructed',sum(c is not None for c in coeff),'nonzero',sum(bool(c) for c in coeff),flush=True)
    if any(c is None for c in coeff):return
    # A few exact fresh rational evaluations cheaply reject reconstruction
    # errors before the complete combinatorial certificate.
    import random
    rng=random.Random(241027)
    for _ in range(5):
        pp=[rng.randint(1,5)]
        for _ in range(n-2):pp.append(sum(pp)+rng.randint(1,10))
        pt=[-sum(pp)]+pp;total=Fraction(0)
        for c,orb in zip(coeff,orbits):
            if not c:continue
            for i in orb:
                u=units[i];a=pt[u['apex']];den=1
                for side,s in u['cuts']:
                    q=sum(pt[j] for j in side);den*=q*(q+s*a)
                total+=c*Fraction((-a)**(n-4),den)
        if total!=Fraction((-1)**(n-1),math.prod(pt)):
            print('RATIONAL RECONSTRUCTION FAILED',flush=True);return
    print('fresh rational evaluations passed',flush=True)
    data={'n':n,'orbits':orbits,'coefficients':[str(c) for c in coeff],'representatives':units,
          'status':'RATIONAL_EVALUATION_CANDIDATE'}
    path=here/f'nc_top_{n}.json';path.write_text(json.dumps(data,indent=2)+'\n')
    e=[tuple(int(i==j) for i in range(n)) for j in range(n)];out=defaultdict(Fraction)
    for j,(c,orb) in enumerate(zip(coeff,orbits)):
        if not c:continue
        for i in orb:
            u=units[i];h=sub(e[u['root']],e[u['apex']]);gs=tuple(sorted(sub(e[a],e[b]) for a,b in u['edges']))
            for flag,v in pyramid(h,gs).items():out[flag]+=c*Fraction(v)
        if j%10==0:print('flags orbit',j,'elapsed',time.time()-start,flush=True)
    target=simplex(tuple(e));bad={k:out.get(k,0)-target.get(k,0) for k in set(out)|set(target) if out.get(k,0)!=target.get(k,0)}
    data.update(status='ALL_COMPLETE_FLAGS_EQUAL' if not bad else 'COMPLETE_FLAG_COUNTEREXAMPLE',
                flag_discrepancies=len(bad),elapsed_seconds=time.time()-start,
                support_units=sum(len(o) for c,o in zip(coeff,orbits) if c))
    path.write_text(json.dumps(data,indent=2)+'\n')
    print('DONE',data['status'],'units',data['support_units'],'elapsed',time.time()-start,flush=True)
if __name__=='__main__':main()
