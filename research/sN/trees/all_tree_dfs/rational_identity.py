#!/usr/bin/env python3
"""Exact identities between products of affine linear rational functions.

Eliminate one variable at a time. All principal-part coefficients at every
pole must vanish. If the remaining polynomial part has degree at most D,
its values at D+1 distinct constant sections must vanish too. For a proper
rational function there is no polynomial part. Coefficients are Fractions;
there is no sampling or numerical rank assumption in this verification.

Term: c * num**power / product(form**multiplicity). A form has d variable
coefficients followed by its constant. Canonicalization cancels equal factors.
The command checks a saved NC coefficient proposal, with a 150-second budget.
"""
import sys,json,time,math
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict,Counter

def canonical(form):
    form=tuple(map(Q,form))
    if not any(form):return Q(0),tuple(0 for _ in form)
    lcm=math.lcm(*(x.denominator for x in form))
    ints=[int(x*lcm) for x in form];g=math.gcd(*ints)
    if next(x for x in ints if x)<0:g=-g
    return Q(g,lcm),tuple(x//g for x in ints)

def term(c,num,k,den):
    c=Q(c);dim=len(num)-1;one=(0,)*dim+(1,)
    scale,num=canonical(num)
    if k:
        c*=scale**k
        if not c:return None
        if not any(num[:-1]):c*=Q(num[-1])**k;num=one;k=0
    else:num=one
    dd=Counter()
    for f,p in den:
        scale,f=canonical(f)
        assert scale,'identically zero denominator'
        c/=scale**p
        if not any(f[:-1]):c/=Q(f[-1])**p
        else:dd[f]+=p
    cancel=min(k,dd.get(num,0));k-=cancel;dd[num]-=cancel
    if not k:num=one
    key=(num,k,tuple(sorted((f,p) for f,p in dd.items() if p)))
    return key,c

def add(out,c,num,k,den):
    t=term(c,num,k,den)
    if t is not None and t[1]:out[t[0]]+=t[1]

def subst(form,j,section):
    return tuple(Q(x)+Q(form[j])*s for i,(x,s) in enumerate(zip(form[:j]+form[j+1:],section)))

class Verifier:
    def __init__(self,budget=150):self.start=time.time();self.budget=budget;self.memo=set();self.calls=0;self.depthmax=0
    def check(self,expr,depth=0):
        self.calls+=1;self.depthmax=max(self.depthmax,depth)
        if time.time()-self.start>self.budget:raise TimeoutError('symbolic verification budget')
        expr={t:c for t,c in expr.items() if c}
        if not expr:return True
        scale=next(iter(expr.values()));ck=tuple(sorted((t,c/scale) for t,c in expr.items()))
        if ck in self.memo:return True
        if len(expr)==1:return False
        d=len(next(iter(expr))[0])-1
        if not d:return sum(expr.values())==0
        # Prefer a variable with few pole occurrences. This is a proof-order
        # choice only; no forms or terms are excluded.
        counts=[]
        for j in range(d):
            forms={f for num,k,den in expr for f,p in den if f[j]}
            occ=sum(sum(bool(f[j]) for f,p in den) for num,k,den in expr)
            counts.append((occ,len(forms),j))
        _,_,j=min(counts)
        children=defaultdict(lambda:defaultdict(Q));D=-1
        for term_no,((num,k,den),c) in enumerate(expr.items()):
            if term_no%64==0 and time.time()-self.start>self.budget:
                raise TimeoutError('symbolic verification budget')
            dt=sum(p for f,p in den if f[j]);D=max(D,(k if num[j] else 0)-dt)
            for f,r in den:
                if not f[j]:continue
                section=tuple(-Q(x,f[j]) for x in f[:j]+f[j+1:])
                nn=subst(num,j,section)
                rest=[(g,p) for g,p in den if g!=f]
                # Taylor coefficient of the numerator at this pole.
                states=[]
                for ell in range(min(k,r-1)+1):
                    a=c*math.comb(k,ell)*Q(num[j])**ell/Q(f[j])**r
                    if a:states.append((ell,a,nn,k-ell,[]))
                for g,p in rest:
                    gg=subst(g,j,section);new=[]
                    for s,a,n0,k0,ds in states:
                        for ell in range(r-s):
                            b=a*(-1)**ell*math.comb(p+ell-1,ell)*Q(g[j])**ell
                            if b:new.append((s+ell,b,n0,k0,ds+[(gg,p+ell)]))
                    states=new
                for s,a,n0,k0,ds in states:add(children[(f,r-s)],a,n0,k0,ds)
        if self.calls%1000==0:print('symbolic calls',self.calls,'depth',depth,'terms',len(expr),'elapsed',time.time()-self.start,flush=True)
        for child in children.values():
            if not self.check(child,depth+1):return False
        if D>=0:
            # Avoid constant sections on which a denominator becomes the zero
            # polynomial. There are finitely many, so D+1 valid sections exist.
            used=0;t=0
            while used<=D:
                section=(Q(0),)*(d-1)+(Q(t),);t+=1
                if any(not any(subst(f,j,section)) for num,k,den in expr for f,p in den):continue
                child=defaultdict(Q)
                for (num,k,den),c in expr.items():
                    add(child,c,subst(num,j,section),k,[(subst(f,j,section),p) for f,p in den])
                if not self.check(child,depth+1):return False
                used+=1
        self.memo.add(ck);return True

def selftest():
    # 1/(xy) = [1/x + 1/y]/(x+y), including repeated-pole derivative control.
    x=(1,0,0);y=(0,1,0);s=(1,1,0);one=(0,0,1)
    e=defaultdict(Q);add(e,1,one,0,[(x,1),(y,1)]);add(e,-1,one,0,[(x,1),(s,1)]);add(e,-1,one,0,[(y,1),(s,1)])
    assert Verifier().check(e)
    e=defaultdict(Q);add(e,1,s,2,[(x,2)]);add(e,-1,one,0,[]);add(e,-2,y,1,[(x,1)]);add(e,-1,y,2,[(x,2)])
    assert Verifier().check(e)
    add(e,1,one,0,[]);assert not Verifier().check(e)

def main():
    selftest();n=int(sys.argv[1]);here=Path(__file__).parent
    if n==6:
        d=json.loads((here/f'nc_top_{n}.json').read_text());units=d['representatives'];cs=list(map(Q,d['coefficients']));orbits=d['orbits']
    else:
        d=json.loads((here/f'nc_fast_{n}.json').read_text());units=d['units'];cs=list(map(Q,d['coefficient_proposal']));orbits=d['orbits']
    fs=[tuple(int(i==j) for i in range(n-1))+(0,) for j in range(n-1)]+[(-1,)*(n-1)+(0,)]
    one=(0,)*(n-1)+(1,);expr=defaultdict(Q)
    for c,o in zip(cs,orbits):
        if not c:continue
        for idx in o:
            u=units[idx];a=fs[u['apex']];den=[]
            for side,sgn in u['cuts']:
                q=tuple(sum(fs[i][j] for i in side) for j in range(n))
                den.extend([(q,1),(tuple(x+sgn*y for x,y in zip(q,a)),1)])
            add(expr,c,tuple(-x for x in a),n-4,den)
    add(expr,-((-1)**(n-1)),one,0,[(f,1) for f in fs])
    print('n',n,'terms',len(expr),'budget',150,flush=True)
    v=Verifier();status='UNRESOLVED'
    try:status='EXACT_RATIONAL_IDENTITY' if v.check(expr) else 'NOT_AN_IDENTITY'
    except TimeoutError:status='BUDGET_EXHAUSTED'
    result={'n':n,'status':status,'calls':v.calls,'memoized_identities':len(v.memo),'max_depth':v.depthmax,'elapsed_seconds':time.time()-v.start}
    (here/f'nc_rational_identity_{n}.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
if __name__=='__main__':main()
