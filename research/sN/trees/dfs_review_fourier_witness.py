#!/usr/bin/env python3
"""Propose rational Fourier relations from modular linear algebra, then check fresh exact points.
This is a rational point-check, not a symbolic identity certificate.
"""
from dfs_review_fourier import *
from sympy.polys.modulargcd import _integer_rational_reconstruction
from sympy.polys.domains import ZZ
m=int(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'nopath';count=int(sys.argv[3]) if len(sys.argv)>3 else 45
fam=family(m,mode);perms=list(itertools.permutations(range(m)));pts=list(points(m,count));start=time.time()
A=np.array([[orbit_mod(u,p,m,perms) for u in fam]+[pow(math.prod(p)%P,P-2,P)] for p in pts],dtype=np.int64)
r=0;piv=[]
for c in range(len(fam)):
 nz=np.flatnonzero(A[r:,c])
 if not len(nz):continue
 j=r+int(nz[0]);A[[r,j]]=A[[j,r]];A[r]=A[r]*pow(int(A[r,c]),P-2,P)%P
 col=A[:,c].copy();col[r]=0;A=(A-col[:,None]*A[r][None,:])%P
 piv.append(c);r+=1
 if r==len(A):break
assert not any(A[j,-1] for j in range(r,len(A)))
cs=[Fraction(0) for _ in fam]
for j,c in enumerate(piv):
 q=_integer_rational_reconstruction(ZZ(int(A[j,-1])),ZZ(P),ZZ)
 if q is None:raise ValueError('reconstruction failed')
 cs[c]=Fraction(str(q))
print('proposal',[(i,str(c)) for i,c in enumerate(cs) if c],flush=True)
checks=[]
for t,pt in enumerate(list(points(m,count+10))[-10:]):
 got=sum(c*orbit_exact(u,pt,m,perms) for c,u in zip(cs,fam) if c);target=Fraction(1,math.prod(pt))
 print('fresh exact',t,got==target,'elapsed',round(time.time()-start,2),flush=True)
 checks.append(got==target)
 if got!=target:break
out=dict(m=m,mode=mode,coefficients=[str(c) for c in cs],representatives=fam,exact_fresh_point_checks=checks,status='POINT_IDENTITY_ONLY_NOT_SYMBOLIC')
(HERE/f'dfs_review_fourier_witness_{m}_{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
