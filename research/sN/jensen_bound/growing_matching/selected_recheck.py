#!/usr/bin/env python3
"""Rebuild/check the new generic selected-q-matching counting leaf only."""
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
MODULE='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected'
SOURCE=MODULE.replace('.','/')+'.lean'
DRIVER='verification/frontier/GrowingMatchingSelectedCheck.lean'
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
    (OUT/('selected_'+tag+'.log')).write_text(proc.stdout)
    (OUT/('selected_'+tag+'.exit')).write_text(str(proc.returncode)+'\n')
    results.append({'command':command,'exit_code':proc.returncode})
    if proc.returncode:
        print(proc.stdout)
        raise SystemExit(proc.returncode)
text=(OUT/'selected_exact.log').read_text()
checks={name:sorted(a.strip() for a in axes.split(',') if a.strip())
    for name,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
short=['exact_card_contract','exact_fraction_contract','one_edge_full_prefix',
    'empty_ground_zero_request','oversized_request']
long=['containment_card_mul_descFactorial','matchingVertices_card',
    'selectedEvent_card_mul_le_matchings','selectedEvent_card_mul_le_choose',
    'selectedEvent_fraction_le_choose','selectedEvent_fraction_le']
expected={'GrowingMatchingSelectedCheck.'+x for x in short}|{
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
    'scope':'Actual uniform label-to-position permutations on Fin n; arbitrary finite simple graph with ordinary unordered Sym2 edges, all natural q including0/oversized and every k<=n.',
    'result':'Pr[selected k labels contain q vertex-disjoint edges] <= eta^q/q! * (k)_(2q)/(n)_(2q). Stronger natural cardinal bounds retain the exact number of matchings or choose(eta,q).',
    'semantic_checks':['Selected vertices are the actual preimage of the first k positions.',
        'Matchings are actual q-element subsets of edgeFinset with disjoint endpoint sets.',
        'The endpoint union has exactly2q vertices.',
        'The exact finite containment law is proved through actual UniformTuples, not assumed.',
        'The factorial follows from q!*choose(eta,q)=(eta)_q<=eta^q.',
        'Oversized events are explicitly empty; real denominators may be zero only there.',
        'Independent expanded consumer states the literal existential event without matchings or selectedEvent.',
        'One-edge/full-prefix, empty-ground/q0, and oversized controls are kernel verified.'],
    'not_claimed':['No new unconditional neural-network width theorem or exponential bound.',
        'No published source or public aggregator was edited.'],
    'commands':results,'axiom_checks':checks,'allowed_axioms':sorted(allowed),
    'log_sha256':{str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
        for tag,_ in commands for suffix in ['log','exit']
        for p in [OUT/('selected_'+tag+'.'+suffix)]}}
(OUT/'selected_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','source_files':len(before),'axiom_checks':len(checks)}))
