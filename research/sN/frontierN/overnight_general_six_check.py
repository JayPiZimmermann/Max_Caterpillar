"""Independent complete finite check of the six-row bowtie classification.

No producer imports. Independently enumerates support multisets and sign classes,
uses highest-priority-first flags (the producer uses lowest-priority-first),
computes active components by bitset graph reachability, and verifies recorded
cut-removal witnesses. All linear matrices have <=6 columns and entries0/1.
Every square minor has absolute determinant<=6!=720<1009; consequently rank and
row-span calculations mod1009 are EXACT over Q, including augmented matrices.
This determinant bound is essential; generic modular rank gaps would not suffice.
"""
from itertools import combinations,combinations_with_replacement,permutations,product
from pathlib import Path
import json,math,time,hashlib

P=1009
assert P>math.factorial(6) and all(P%d for d in range(2,math.isqrt(P)+1))
BASE=Path(__file__).with_suffix('')

def equations(bits):
    rows=[]
    while bits:
        bit=bits&-bits;k=bit.bit_length()-1;bits-=bit
        c=k//2+1;rows.append([int(bool(c&(1<<i))) for i in range(5)]+[k%2])
    return rows

def echelon(bits):
    rows=equations(bits);piv={};k=0
    for col in range(5):
        found=next((i for i in range(k,len(rows)) if rows[i][col]),None)
        if found is None:continue
        rows[k],rows[found]=rows[found],rows[k]
        inv=pow(rows[k][col],P-2,P);rows[k]=[x*inv%P for x in rows[k]]
        for i in range(len(rows)):
            if i==k:continue
            q=rows[i][col]
            if q:rows[i]=[(x-q*y)%P for x,y in zip(rows[i],rows[k])]
        piv[col]=rows[k];k+=1
    if any(not any(r[:5]) and r[5] for r in rows):return None
    return piv

def implied(piv,C,rhs):
    row=[int(bool(C&(1<<i))) for i in range(5)]+[rhs]
    for col in sorted(piv):
        q=row[col]
        row=[(x-q*y)%P for x,y in zip(row,piv[col])]
    return not any(row)

def components(supports,active):
    adjacent=[1<<i for i in range(5)]
    for j,sup in enumerate(supports):
        if active&(1<<j):
            for i in range(5):
                if sup&(1<<i):adjacent[i]|=sup
    unseen=31;out=[]
    while unseen:
        reached=unseen&-unseen
        while True:
            new=reached
            for i in range(5):
                if reached&(1<<i):new|=adjacent[i]
            if new==reached:break
            reached=new
        out.append(reached);unseen&=~reached
    return out

def prep(fam):
    supports=[sum(1<<i for i in s) for s in fam]
    eq=[]
    for active in range(64):
        comps=components(supports,active)
        eq.append([sum((1 << (2*(C-1)+int(bool(C&(1<<a))))) for C in comps) for a in range(5)])
    neg=[];full=[]
    for priority in permutations(range(5)):
        leaders=[sup.index(next(i for i in priority if i in sup)) for sup in fam]
        neg.append((leaders,priority[-1]))
        for eps in product((-1,1),repeat=5):
            lead_signs=[eps[sup[k]] for sup,k in zip(fam,leaders)]
            a=next((i for i in priority if eps[i]>0),priority[-1])
            full.append((leaders,lead_signs,a))
    return supports,eq,neg,full

def cut_check(fam,signs,active,C,j):
    crossing=[]
    for k,sup in enumerate(fam):
        if not(active&(1<<k)):continue
        count=sum(bool(C&(1<<i)) for i in sup)
        if 0<count<len(sup):crossing.append(k)
    assert crossing==[j]
    inside=[z for i,z in zip(fam[j],signs[j]) if C&(1<<i)]
    outside=[z for i,z in zip(fam[j],signs[j]) if not(C&(1<<i))]
    assert inside and outside
    assert min(inside)==max(inside) or min(outside)==max(outside)
    return active&~(1<<j)

def check_pair(fam,signs,seen,cert):
    active=cert['active'];a=cert['winner_a'];b=cert['winner_b']
    assert a!=b and (active,a) in seen and (active,b) in seen
    for C,j in cert['steps']:
        assert bool(C&(1<<a))==bool(C&(1<<b))
        active=cut_check(fam,signs,active,C,j)
    C=cert['separating_cut'];assert bool(C&(1<<a))!=bool(C&(1<<b))
    for j,sup in enumerate(fam):
        if active&(1<<j):assert all(C&(1<<i) for i in sup) or all(not(C&(1<<i)) for i in sup)

def check_global(fam,signs,seen,eq,bits,cert):
    cells=seen
    for changes in cert['rounds']:
        piv=echelon(bits);assert piv is not None
        change={(r['active'],r['winner']):r['steps'] for r in changes}
        assert len(change)==len(changes) and set(change)<=cells
        newcells=set()
        for initial,a in cells:
            active=initial
            for C,j in change.get((initial,a),[]):
                assert implied(piv,C,int(bool(C&(1<<a))))
                active=cut_check(fam,signs,active,C,j)
            newcells.add((active,a));bits|=eq[active][a]
        cells=newcells
    assert echelon(bits) is None

def main():
    start=time.monotonic();root=Path(__file__).parent
    paths=[root/'overnight_general_six_supports.json',root/'overnight_general_six_pairpeeling.json',root/'overnight_general_six_global.json']
    raw=[p.read_bytes() for p in paths];src,pair,glob=map(json.loads,raw)
    families=src['families'];assert len(families)==43
    # Independent support coverage using bitmask subsets and coordinate actions.
    supp=[i for i in range(1,32) if i.bit_count()>=2]
    tests=[(sum(1<<i for i in t),None) for t in combinations(range(5),3)]
    tests +=[(sum(1<<i for i in t),a) for t in combinations(range(5),4) for a in t]
    masks={s:sum(1<<k for k,(t,a) in enumerate(tests) if s&t==s and (a is None or s&(1<<a))) for s in supp}
    allcovers=set();full_cover=(1<<len(tests))-1
    for inds in combinations_with_replacement(supp,6):
        cover=0
        for i in inds:cover|=masks[i]
        if cover==full_cover:allcovers.add(inds)
    covered=set()
    for rec in families:
        fam=rec['family'];orbit=set()
        for p in permutations(range(5)):
            orbit.add(tuple(sorted(sum(1<<p[i] for i in s) for s in fam)))
        assert orbit<=allcovers and not(orbit&covered)
        covered|=orbit
    assert covered==allcovers and len(covered)==2767
    certs={}
    for rec in pair['completed']:
        for item in rec['excluded']:
            key=(rec['family_index'],tuple(map(tuple,item['signs'])))
            assert key not in certs;certs[key]=item['certificate']
    globalcerts={(glob['family_index'],tuple(map(tuple,c['signs']))):c for c in glob['certificates']}
    used_pairs=set();used_global=set();counts={'negative_flags':0,'full_flags':0,'pair_cuts':0,'global_cuts':0,'bowties':0};total=0
    for fi,rec in enumerate(families):
        fam=rec['family'];supports,eq,neg,full=prep(fam);cache={};local={k:0 for k in counts}
        choices=[[s for s in product((-1,1),repeat=len(sup)) if min(s)<max(s)] for sup in fam]
        for signs in product(*choices):
            total+=1;bits=0
            for leaders,a in neg:
                active=0
                for j,k in enumerate(leaders):
                    if signs[j][k]<0:active|=1<<j
                bits|=eq[active][a]
            if bits not in cache:cache[bits]=echelon(bits)
            if cache[bits] is None:local['negative_flags']+=1;continue
            seen=set()
            for leaders,eps,a in full:
                active=0
                for j,k in enumerate(leaders):
                    if signs[j][k]*eps[j]>0:active|=1<<j
                seen.add((active,a));bits|=eq[active][a]
            if bits not in cache:cache[bits]=echelon(bits)
            if cache[bits] is None:local['full_flags']+=1;continue
            key=(fi,signs)
            if key in certs:
                check_pair(fam,signs,seen,certs[key]);used_pairs.add(key);local['pair_cuts']+=1;continue
            if key in globalcerts:
                check_global(fam,signs,seen,eq,bits,globalcerts[key]);used_global.add(key);local['global_cuts']+=1;continue
            assert fam==[[0,1],[0,2],[0,3],[0,4],[1,2],[3,4]]
            assert signs[:4]==((-1,1),)*4
            piv=cache[bits];assert len(piv)==5
            assert all(implied(piv,1<<i,int(i==0)) for i in range(5))
            local['bowties']+=1
        for k,v in local.items():counts[k]+=v
        print('family',fi,local,flush=True)
    assert used_pairs==set(certs) and used_global==set(globalcerts)
    assert counts=={'negative_flags':55839,'full_flags':1300,'pair_cuts':1031,'global_cuts':2,'bowties':4}
    assert total==58176
    result={'status':'PASS: complete real-coefficient support/sign classification via exact finite necessities',
        'support_multisets':len(allcovers),'support_orbits':43,'coefficient_sign_profiles':total,'counts':counts,
        'rank_arithmetic':{'prime':P,'max_columns':6,'entry_bound':1,'all_minor_abs_bound':math.factorial(6)},
        'hashes':{p.name:hashlib.sha256(r).hexdigest() for p,r in zip(paths,raw)},
        'seconds':time.monotonic()-start,'scope':'Finite classification plus written cell/span bridge; not Lean verified.'}
    BASE.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
