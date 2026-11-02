#!/usr/bin/env python3
"""Rebuild/check the new generic matching embedding transport leaf only."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
MODULE='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Transport'
SOURCE=MODULE.replace('.','/')+'.lean'
DRIVER='verification/frontier/GrowingMatchingTransportCheck.lean'
SELF=str(Path(__file__).resolve().relative_to(ROOT))
spec=importlib.util.spec_from_file_location('source_verifier',ROOT/'scripts/verify.py')
parser=importlib.util.module_from_spec(spec)
spec.loader.exec_module(parser)
def digest(p): return sha256((ROOT/p).read_bytes()).hexdigest()
def sources():
    found=set(); todo=[SOURCE,DRIVER]
    while todo:
        name=todo.pop()
        if name in found: continue
        path=ROOT/name
        if not path.is_file(): continue
        found.add(name)
        for imported in re.findall(r'^import\s+([^\n]+)',parser.uncomment(path.read_text()),re.M):
            todo.extend(m.replace('.','/')+'.lean' for m in imported.split())
    found.update([SELF,'scripts/verify.py','scripts/lean_lock.sh',
        'research/sN/zulip_three/lean_small_pool.py','lake-manifest.json','lean-toolchain'])
    return {p:digest(p) for p in sorted(found)}
before=sources()
small=['python3','research/sN/zulip_three/lean_small_pool.py']
cached='--cached' in sys.argv
(ROOT/'.lake/build/lib/MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching').mkdir(parents=True,exist_ok=True)
commands=[('build',small+['lake','env','lean','-j1','-o',
    '.lake/build/lib/'+SOURCE.removesuffix('.lean')+'.olean',SOURCE] if cached else
    ['scripts/lean_lock.sh','lake','build',MODULE]),
    ('exact',small+['lake','env','lean','-j1',DRIVER])]
results=[]
for tag,command in commands:
    proc=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/('transport_'+tag+'.log')).write_text(proc.stdout)
    (OUT/('transport_'+tag+'.exit')).write_text(str(proc.returncode)+'\n')
    results.append({'command':command,'exit_code':proc.returncode})
    if proc.returncode:
        print(proc.stdout)
        raise SystemExit(proc.returncode)
text=(OUT/'transport_exact.log').read_text()
checks={name:sorted(a.strip() for a in axes.split(',') if a.strip())
    for name,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
short=['exact_transport_contract','exact_event_contract','identity_transport']
long=['edgeVertices_map','mapMatching_card','mapMatchingVertices','mapped_edge_mem',
    'mapMatching_mem','mapMatchingVertices_subset_range','transport_matching',
    'selectedEvent_of_comap_matching']
expected={'GrowingMatchingTransportCheck.'+x for x in short}|{
    'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.'+x for x in long}
assert set(checks)==expected,(set(checks)-expected,expected-set(checks))
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(a)<=allowed for a in checks.values())
assert before==sources(),'Sources changed during check; rerun.'
for p in before:
    if p.endswith('.lean'):
        assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b|Lean\.ofReduceBool',
            parser.uncomment((ROOT/p).read_text())),p
receipt={'status':'PASS','checked_at_utc':datetime.now(timezone.utc).isoformat(),
    'evidence_kind':'owned cached-kernel exact-type gate' if cached else 'canonical module rebuild and exact-type gate',
    'module':MODULE,'driver':DRIVER,'source_sha256':before,'source_unchanged':True,
    'scope':'Actual injective f:Fin m -> Fin n and ordinary finite simple graph G; every actual q-matching of G.comap f maps to an actual q-matching of G, including empty domains/matchings.',
    'result':'The image Sym2 edge set has exactly q edges, its endpoints are exactly the image of the original endpoints, and lie in the actual embedding range. If that range is selected by sigma then the original ambient selectedEvent holds.',
    'semantic_checks':['Edges are actual Sym2.map images, not a newly postulated graph witness.',
        'Embedding injectivity proves injectivity on unordered edges and preserves disjoint endpoint supports.',
        'Local graph adjacency is the actual comap adjacency.',
        'Independent expanded consumer states ordinary edge membership, cardinality, pairwise-disjointness and endpoint containment.',
        'The identity embedding preserves every actual edge set.'],
    'not_claimed':['No new unconditional neural-network width theorem.',
        'No published source or public aggregator was edited.'],
    'commands':results,'axiom_checks':checks,'allowed_axioms':sorted(allowed),
    'log_sha256':{str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
        for tag,_ in commands for suffix in ['log','exit']
        for p in [OUT/('transport_'+tag+'.'+suffix)]}}
(OUT/'transport_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','source_files':len(before),'axiom_checks':len(checks)}))
