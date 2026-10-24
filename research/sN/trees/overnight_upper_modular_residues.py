#!/usr/bin/env python3
"""Exact pole-orbit gate, with independently checked affine invariance.

A homogeneous rational function of negative degree vanishes if every finite
principal part vanishes. Exact invariance under two permutations transports
the principal-part checks over all pole orbits. Each representative is checked
by the existing rational-identity verifier after an exact residue expansion.
"""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import sys
import time

import overnight_upper_modular_exact as E
from rational_identity import Verifier,subst,add

HERE=Path(__file__).parent
OUTPUT=HERE/'overnight_upper_modular_residues.json'


def transform_form(form,permutation):
    n=len(form);raw=[0]*n
    for i,c in enumerate(form[:-1]):raw[permutation[i]]+=c
    reduced=tuple(c-raw[-1] for c in raw[:-1])+(form[-1],)
    g=math.gcd(*reduced)
    if next(x for x in reduced if x)<0:g=-g
    return g,tuple(c//g for c in reduced)


def invariance(expression,permutation):
    forms={num for num,k,den in expression}|{f for num,k,den in expression for f,p in den}
    mapping={f:transform_form(f,permutation) for f in forms};result=defaultdict(Q)
    for (num,k,den),c in expression.items():
        scale,newnum=mapping[num];c*=scale**k;newden=[]
        for f,p in den:
            scale,g=mapping[f];c/=scale**p;newden.append((g,p))
        result[(newnum,k,tuple(sorted(newden)))]+=c
    assert {k:c for k,c in result.items() if c}==expression
    return mapping


def principal_parts(terms,f):
    j=min((abs(v),i) for i,v in enumerate(f[:-1]) if v)[1]
    section=tuple(-Q(x,f[j]) for x in f[:j]+f[j+1:]);children=defaultdict(lambda:defaultdict(Q))
    for (num,k,den),c in terms:
        r=dict(den)[f];nn=subst(num,j,section);rest=[(g,p) for g,p in den if g!=f]
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
        for s,a,n0,k0,ds in states:add(children[r-s],a,n0,k0,ds)
    return {r:{k:c for k,c in child.items() if c} for r,child in children.items()}


def main():
    started=time.monotonic();data=json.loads(E.CRT.read_text());assert data['status']=='RATIONAL_PROPOSAL_PENDING_EXACT_GATE'
    expression,controls=E.build(data)
    assert all(k-sum(p for f,p in den)==-7 for num,k,den in expression)
    # These two permutations generate Aff(F_7). The identity itself is checked,
    # rather than inferred from the producer's claimed orbit structure.
    generators=[[(i+1)%7 for i in range(7)],[(3*i)%7 for i in range(7)]]
    mappings=[invariance(expression,pi) for pi in generators]
    poles={f for num,k,den in expression for f,p in den};seen=set();orbits=[]
    for f in sorted(poles):
        if f in seen:continue
        orbit={f};queue=[f]
        while queue:
            g=queue.pop()
            for mapping in mappings:
                h=mapping[g][1];assert h in poles
                if h not in orbit:orbit.add(h);queue.append(h)
        seen.update(orbit);orbits.append((min(orbit),sorted(orbit)))
    assert seen==poles
    index={f:[] for f,o in orbits}
    for term,c in expression.items():
        for f,p in term[2]:
            if f in index:index[f].append((term,c))
    source_hash=E.base.digest(E.CRT);producer_hash=E.base.digest(Path(__file__))
    out=dict(status='EXACT_POLE_ORBIT_CHECK_IN_PROGRESS',source_sha256=source_hash,
             producer_sha256=producer_hash,decoder_sha256=E.base.digest(Path(E.__file__)),
             verifier_sha256=E.base.digest(HERE/'all_tree_dfs/rational_identity.py'),
             homogeneous_degree=-7,exact_terms=len(expression),pole_count=len(poles),pole_orbits=orbits,
             exact_invariance_generators=generators,independent_unit_controls=controls,completed=[])
    if OUTPUT.exists():
        old=json.loads(OUTPUT.read_text())
        assert all(old[k]==out[k] for k in ('source_sha256','producer_sha256','decoder_sha256','verifier_sha256'))
        out['completed']=old['completed']
    done={tuple(item['pole']) for item in out['completed']}
    print('INVARIANCE PASS','POLES',len(poles),'ORBITS',len(orbits),'SECONDS',time.monotonic()-started,flush=True)
    OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
    for f,orbit in orbits:
        if f in done:continue
        began=time.monotonic();children=principal_parts(index[f],f);v=Verifier(budget=max(1,1000-(time.monotonic()-started)))
        try:ok=all(v.check(child) for child in children.values())
        except TimeoutError:
            out['status']='EXACT_POLE_ORBIT_BUDGET_REACHED_NO_CONCLUSION';break
        if not ok:
            out.update(status='RATIONAL_PROPOSAL_FAILED',failed_pole=f);break
        out['completed'].append(dict(pole=f,orbit_size=len(orbit),input_terms=len(index[f]),
                                     residue_terms={r:len(e) for r,e in children.items()},
                                     symbolic_calls=v.calls,seconds=time.monotonic()-began))
        OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
        print('VERIFIED',len(out['completed']),'/',len(orbits),'POLE',f,'SECONDS',time.monotonic()-started,flush=True)
    if len(out['completed'])==len(orbits):out['status']='EXACT_TOP_IDENTITY'
    out['elapsed_this_run']=time.monotonic()-started
    OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('DONE',out['status'],flush=True)


if __name__=='__main__':main()
