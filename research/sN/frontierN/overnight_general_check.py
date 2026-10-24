"""Independent exact check of the uniform five-row exclusion certificate.

Does not import the producer or solve linear systems.  It independently covers
all support families, checks sign-class coverage, checks the lexicographic row
signs and separating subsets, then checks the recorded rational linear
combinations of equations.  All coefficient magnitudes, including irrational
ones, are covered by the leading-coefficient lemma in overnight_general.md.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import json
import time

def main():
    start=time.monotonic(); path=Path(__file__).with_name('overnight_general_flags.json')
    raw=path.read_bytes(); data=json.loads(raw); assert data['N']==5
    assert data['flag_type']=='negative_lexicographic'
    records=data['results']; vertices=set(range(5))
    support_types={tuple(sorted(tuple(s) for s in rec['family'])) for rec in records}
    assert len(support_types)==3
    # No row with support 0, 1, or 5 can help C3/C4. Repetitions can be removed.
    # Therefore an at-most-five-row family yields a distinct cover of size <=5.
    supports=[frozenset(s) for k in (2,3,4) for s in combinations(range(5),k)]
    tests=[(frozenset(t),None) for t in combinations(range(5),3)]
    tests += [(frozenset(t),a) for t in combinations(range(5),4) for a in t]
    cover=[]
    for s in supports:
        cover.append(sum(1<<i for i,(t,a) in enumerate(tests) if s<=t and (a is None or a in s)))
    full=(1<<len(tests))-1
    orbit={}
    for typ in support_types:
        for p in permutations(range(5)):
            key=tuple(sorted(tuple(sorted(p[i] for i in s)) for s in typ))
            orbit[key]=typ
    cover_counts={}; covered_types=set()
    for k in range(6):
        count=0
        for inds in combinations(range(len(supports)),k):
            mask=0
            for i in inds: mask |= cover[i]
            if mask != full: continue
            count+=1
            assert k==5, ('smaller cover',inds)
            key=tuple(sorted(tuple(sorted(supports[i])) for i in inds))
            assert key in orbit, ('unclassified cover',key)
            covered_types.add(orbit[key])
        cover_counts[k]=count
    assert covered_types==support_types
    classes=equations=0; lengths={}
    for rec in records:
        fam=rec['family']; certs=rec['certificates']
        expected=set(product(*[[s for s in product((-1,1),repeat=len(sup)) if -1 in s and 1 in s] for sup in fam]))
        seen=set()
        assert not rec['survivors']
        for cert in certs:
            signs=tuple(tuple(s) for s in cert['signs']); assert signs in expected and signs not in seen; seen.add(signs)
            total=[Fraction(0)]*6
            for multiplier,(mask,rhs,witness) in cert['contradiction']:
                order,eps,active,winner,subset=witness
                assert set(order)==vertices and len(order)==5
                assert eps==[-1]*5
                rank=[order.index(i) for i in range(5)]
                # Leading coefficient of sum row_i eps_i B**rank_i.
                expected_active=[]
                for j,sup in enumerate(fam):
                    leader=sorted(sup,key=lambda i:rank[i])[-1]
                    if signs[j][sup.index(leader)]*eps[leader]==1: expected_active.append(j)
                assert active==expected_active
                # Coordinate ordering is already stable at B=2.
                assert winner==max(range(5),key=lambda i:eps[i]*(2**rank[i]))
                c=set(subset); assert c and c<=vertices and len(c)==len(subset)
                for j in active:
                    s=set(fam[j]); assert s<=c or s.isdisjoint(c)
                assert mask==sum(1<<i for i in c)
                assert rhs==int(winner in c)
                q=Fraction(multiplier)
                for i in c: total[i]+=q
                total[5]+=q*rhs; equations+=1
            assert total[:5]==[0]*5 and total[5]!=0
            lengths[len(cert['contradiction'])]=lengths.get(len(cert['contradiction']),0)+1
        assert seen==expected and len(seen)==rec['sign_classes']==rec['excluded']
        classes+=len(seen)
    result={'status':'PASS','N':5,'coefficient_sign_classes':classes,
            'checked_equations':equations,'contradiction_lengths':lengths,
            'support_cover_counts':cover_counts,'support_orbits':len(support_types),
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'seconds':time.monotonic()-start,
            'scope':'Uniform real-coefficient cell-condition exclusion; mathematical model bridge in overnight_general.md; not Lean verified.'}
    out=Path(__file__).with_name('overnight_general_check.json')
    out.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__': main()
