"""MEASURED finite-coefficient probe after the exhaustive sign relaxation.

One canonical integer row per coefficient-sign pattern: each positive entry is
the number of negative entries and each negative entry minus the number of
positive entries, then divide the row gcd. Uses modular linear algebra only to
find promising profiles; no modular exclusion is promoted to a rational theorem.
All flags are actual strict cell points for sufficiently large B.
"""
from itertools import permutations,product
from pathlib import Path
import json,time,math

P=1000000007
BASE=Path(__file__).with_suffix('')

def rref(rows,n):
    out=[r[:] for r in rows];piv=[];k=0
    for i in range(n):
        hit=next((j for j in range(k,len(out)) if out[j][i]%P),None)
        if hit is None:continue
        out[k],out[hit]=out[hit],out[k]
        inv=pow(out[k][i]%P,-1,P);out[k]=[(x*inv)%P for x in out[k]]
        for j in range(len(out)):
            if j==k:continue
            f=out[j][i]
            if f:out[j]=[(x-f*y)%P for x,y in zip(out[j],out[k])]
        piv.append(i);k+=1
    return out,piv

def nullspace(rows):
    rr,piv=rref(rows,5)
    out=[]
    for f in range(5):
        if f in piv:continue
        v=[0]*5;v[f]=1
        for j,p in enumerate(piv):v[p]=-rr[j][f]%P
        out.append(v)
    return out

def check(rows,seen):
    kernels={};cons=set()
    for active,a in seen:
        if active not in kernels:kernels[active]=nullspace([rows[j] for j in range(6) if active>>j&1])
        for v in kernels[active]:cons.add(tuple(v+[v[a]]))
    rr,piv=rref(list(cons),5)
    if any(not any(r[:5]) and r[5] for r in rr):return None
    return {'constraint_rank':len(piv),'constraints':len(cons),
            'ell_mod':{str(p):rr[j][5] for j,p in enumerate(piv)}}

def main():
    started=time.monotonic();source=json.loads(Path(__file__).with_name('overnight_general_six_full.json').read_text())
    assert source['complete'];result=[];tested=0
    for rec in source['completed']:
        if not rec['survivors']:continue
        fam=rec['family'];flags=[]
        for perm in permutations(range(5)):
            priority={i:k for k,i in enumerate(perm)}
            leaders=[sup.index(max(sup,key=priority.get)) for sup in fam]
            for eps in product((-1,1),repeat=5):
                roweps=[eps[sup[k]] for sup,k in zip(fam,leaders)]
                winner=max(range(5),key=lambda i:eps[i]*2**priority[i])
                flags.append((leaders,roweps,winner))
        passed=[]
        for signs in rec['survivors']:
            rows=[]
            for sup,s in zip(fam,signs):
                np=s.count(1);nn=s.count(-1);g=math.gcd(np,nn);r=[0]*5
                for i,z in zip(sup,s):r[i]=(nn if z==1 else -np)//g
                rows.append(r)
            seen=set()
            for leaders,eps,a in flags:
                active=sum(1<<j for j,k in enumerate(leaders) if signs[j][k]*eps[j]>0)
                seen.add((active,a))
            ans=check(rows,seen);tested+=1
            if ans is not None:passed.append({'signs':signs,'rows':rows,'diagnostic':ans})
        result.append({'family_index':rec['family_index'],'family':fam,'tested':len(rec['survivors']), 'passed':passed})
        BASE.with_suffix('.json').write_text(json.dumps({'status':'MEASURED finite representative probe; modular consistency only',
            'tested':tested,'passed':sum(len(r['passed']) for r in result),'families':result,'seconds':time.monotonic()-started},indent=2)+'\n')
        print('family',rec['family_index'],'tested',len(rec['survivors']),'passed',len(passed),flush=True)

if __name__=='__main__':main()
