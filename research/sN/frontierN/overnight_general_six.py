"""Bounded exhaustive support/sign relaxation for six zero-sum first rows.

Support multisets of size six include duplicates and full five-coordinate
supports. Exact finite necessary conditions C3/C4 and negative lexicographic
component equations; a surviving profile is NOT a construction. Consistency
is computed mod1009: every square minor has order<=6 and entries0/1, so its
absolute determinant<=6!<1009. Hence these ranks equal rational ranks exactly.
Runs one bounded phase and preserves each completed family in JSON.
"""
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path
import argparse,json,time,math

N=5; P=1009
BASE=Path(__file__).with_suffix('')
SUPPORTS=[tuple(c) for k in (2,3,4,5) for c in combinations(range(N),k)]
PERMS=list(permutations(range(N)))

def support_phase():
    start=time.monotonic(); ss=list(map(set,SUPPORTS)); index={s:i for i,s in enumerate(SUPPORTS)}
    tests=[(set(t),None) for t in combinations(range(N),3)]
    tests +=[(set(t),a) for t in combinations(range(N),4) for a in t]
    masks=[sum(1<<i for i,(t,a) in enumerate(tests) if s<=t and (a is None or a in s)) for s in ss]
    full=(1<<len(tests))-1; covers=set()
    for inds in combinations_with_replacement(range(len(SUPPORTS)),6):
        mask=0
        for i in inds:mask|=masks[i]
        if mask==full:covers.add(inds)
    total=len(covers); maps=[[index[tuple(sorted(p[i] for i in s))] for s in SUPPORTS] for p in PERMS]
    families=[]
    while covers:
        inds=min(covers)
        orbit={tuple(sorted(mp[i] for i in inds)) for mp in maps}
        assert orbit<=covers
        covers-=orbit
        fam=[SUPPORTS[i] for i in inds]
        classes=math.prod(2**len(s)-2 for s in fam)
        families.append({'family':fam,'labelled_orbit_size':len(orbit),'sign_classes':classes})
    result={'support_multisets':total,'family_orbits':len(families),'families':families,
            'total_sign_profiles':sum(f['sign_classes'] for f in families),'seconds':time.monotonic()-start}
    BASE.with_name(BASE.name+'_supports.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='families'},flush=True)

def consistent(bits):
    piv={}
    while bits:
        b=bits&-bits; k=b.bit_length()-1;bits-=b
        mask=k//2+1; rhs=k%2
        row=[int(bool(mask>>i&1)) for i in range(5)]+[rhs]
        for i in range(5):
            if not row[i]:continue
            if i not in piv:
                inv=pow(row[i],-1,P);piv[i]=[(v*inv)%P for v in row];break
            f=row[i];row=[(v-f*w)%P for v,w in zip(row,piv[i])]
        else:
            if row[-1]:return False
    return True

def family_check(fam, profiles=None, full=False):
    # For each active subset, precompute all components, then equation bitsets.
    equations=[]
    for active in range(64):
        blocks=[{i} for i in range(5)]
        for j,sup in enumerate(fam):
            if not(active>>j&1):continue
            s=set(sup);hit=[b for b in blocks if b&s]
            blocks=[b for b in blocks if not b&s]+[set().union(*hit)]
        masks=[sum(1<<i for i in b) for b in blocks]
        equations.append([sum(1<<(2*(m-1)+int(bool(m>>a&1))) for m in masks) for a in range(5)])
    flags=[]
    for p in PERMS:
        priority={i:k for k,i in enumerate(p)}
        leaders=[sup.index(max(sup,key=priority.get)) for sup in fam]
        if not full: flags.append((leaders,p[0]))
        else:
            for eps in product((-1,1),repeat=5):
                signs=[eps[sup[k]] for sup,k in zip(fam,leaders)]
                winner=max(range(5),key=lambda i:eps[i]*2**priority[i])
                flags.append((leaders,signs,winner))
    choices=[[s for s in product((-1,1),repeat=len(sup)) if -1 in s and 1 in s] for sup in fam]
    survivors=[];cache={};excluded=0
    for signs in product(*choices) if profiles is None else profiles:
        bits=0
        if full:
            for leaders,eps,a in flags:
                active=sum(1<<j for j,k in enumerate(leaders) if signs[j][k]*eps[j]>0)
                bits |=equations[active][a]
        else:
            for leaders,a in flags:
                active=sum(1<<j for j,k in enumerate(leaders) if signs[j][k]<0)
                bits |=equations[active][a]
        if bits not in cache:cache[bits]=consistent(bits)
        if cache[bits]:survivors.append(signs)
        else:excluded+=1
    return {'excluded':excluded,'survivors':survivors,'distinct_equation_sets':len(cache)}

def sign_phase(seconds,full=False):
    start=time.monotonic()
    source=json.loads(BASE.with_name(BASE.name+('_signs.json' if full else '_supports.json')).read_text())
    families=source['completed'] if full else source['families']
    path=BASE.with_name(BASE.name+('_full.json' if full else '_signs.json'))
    out=json.loads(path.read_text()) if path.exists() else {'completed':[]}
    for i in range(len(out['completed']),len(families)):
        f=families[i]; t=time.monotonic()
        r=family_check(f['family'],f['survivors'] if full else None,full)
        previous_excluded=f.get('excluded',0) if full else 0
        r['excluded']+=previous_excluded
        f={k:v for k,v in f.items() if k not in ['excluded','survivors','distinct_equation_sets','seconds']}
        r.update(f);r['family_index']=i;r['seconds']=time.monotonic()-t
        out['completed'].append(r);out['complete']=len(out['completed'])==len(families)
        path.write_text(json.dumps(out,indent=2)+'\n')
        print('family',i,'sizes',[len(s) for s in f['family']],'classes',f['sign_classes'],
              'survivors',len(r['survivors']),'sec',round(r['seconds'],3),flush=True)
        if time.monotonic()-start>seconds:break

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('phase',choices=['supports','signs','full']);ap.add_argument('--seconds',type=float,default=100)
    a=ap.parse_args();support_phase() if a.phase=='supports' else sign_phase(a.seconds,a.phase=='full')
