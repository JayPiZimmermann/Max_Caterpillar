#!/usr/bin/env python3
"""Self-contained exact replay from the compact combinatorial certificate.

No proposal matrices, full family inventory, or binary engine are read.
Membership is checked unit-by-unit, rational functions use direct DFS cuts,
and all pole-orbit principal parts are checked exactly.
"""
from pathlib import Path
import hashlib
import json
import time

import overnight_upper_affine_certificate as C
from overnight_upper_modular_residues import invariance,principal_parts
from rational_identity import Verifier

HERE=Path(__file__).parent
OUTPUT=HERE/'overnight_upper_affine_verified_7.json'


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    started=time.monotonic();data=json.loads(C.OUTPUT.read_text());expression=C.expression(data)
    assert all(k-sum(p for f,p in den)==-7 for num,k,den in expression)
    h=hashlib.sha256()
    for term,c in sorted(expression.items()):h.update(repr((term,str(c))).encode());h.update(b'\n')
    generators=[[(i+1)%7 for i in range(7)],[(3*i)%7 for i in range(7)]]
    mappings=[invariance(expression,pi) for pi in generators]
    poles={f for num,k,den in expression for f,p in den};seen=set();orbits=[]
    for f in sorted(poles):
        if f in seen:continue
        orbit={f};queue=[f]
        while queue:
            g=queue.pop()
            for mapping in mappings:
                image=mapping[g][1];assert image in poles
                if image not in orbit:orbit.add(image);queue.append(image)
        seen.update(orbit);orbits.append((min(orbit),sorted(orbit)))
    assert seen==poles
    index={f:[] for f,o in orbits}
    for term,c in expression.items():
        for f,p in term[2]:
            if f in index:index[f].append((term,c))
    out=dict(status='COMPACT_EXACT_CHECK_IN_PROGRESS',certificate_sha256=digest(C.OUTPUT),
             producer_sha256=digest(Path(__file__)),decoder_sha256=digest(Path(C.__file__)),
             residue_checker_sha256=digest(HERE/'overnight_upper_modular_residues.py'),
             rational_checker_sha256=digest(HERE/'all_tree_dfs/rational_identity.py'),
             expression_sha256=h.hexdigest(),exact_terms=len(expression),selected_units=data['selected_units'],
             graph_witnesses=len(data['graph_witnesses']),orbit_count=len(data['orbit_records']),
             homogeneous_degree=-7,exact_invariance_generators=generators,pole_count=len(poles),
             pole_orbits=orbits,completed=[])
    if OUTPUT.exists():
        old=json.loads(OUTPUT.read_text())
        assert all(old[k]==out[k] for k in ('certificate_sha256','producer_sha256','decoder_sha256',
                                          'residue_checker_sha256','rational_checker_sha256','expression_sha256'))
        out['completed']=old['completed']
    done={tuple(item['pole']) for item in out['completed']}
    print('COMPACT MEMBERSHIP, DFS, INVARIANCE PASS','TERMS',len(expression),'POLE ORBITS',len(orbits),flush=True)
    OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
    for f,orbit in orbits:
        if f in done:continue
        began=time.monotonic();children=principal_parts(index[f],f);v=Verifier(budget=max(1,1000-(time.monotonic()-started)))
        try:ok=all(v.check(child) for child in children.values())
        except TimeoutError:out['status']='COMPACT_EXACT_BUDGET_REACHED_NO_CONCLUSION';break
        if not ok:out.update(status='COMPACT_WITNESS_FAILED',failed_pole=f);break
        out['completed'].append(dict(pole=f,orbit_size=len(orbit),input_terms=len(index[f]),
                                     residue_terms={r:len(e) for r,e in children.items()},
                                     symbolic_calls=v.calls,seconds=time.monotonic()-began))
        OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
        print('VERIFIED',len(out['completed']),'/',len(orbits),'SECONDS',time.monotonic()-started,flush=True)
    if len(out['completed'])==len(orbits):out['status']='EXACT_TOP_IDENTITY_FROM_COMPACT_WITNESS'
    out['elapsed_this_run']=time.monotonic()-started
    OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('DONE',out['status'],flush=True)


if __name__=='__main__':main()
