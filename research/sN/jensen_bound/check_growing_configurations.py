"""Rebuild and verify arbitrary-arity configuration geometry, deletion and uniform transport.

Run under the shared count65 small Lean lock.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
MODULE='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations'
DRIVER=Path('verification/h2audit/GrowingConfigurationsCheck.lean')
PREFIX='growing_configurations'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def run(tag,args):
    result=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (HERE/f'{PREFIX}_{tag}.log').write_text(result.stdout)
    (HERE/f'{PREFIX}_{tag}.exit').write_text(str(result.returncode)+'\n')
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout

run('module',['lake','build',MODULE])
log=run('exact',['lake','env','lean','-j1',str(DRIVER)])
checks=[]
for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
    got={x.strip() for x in axioms.split(',') if x.strip()}
    assert got<=ALLOWED,(name,got)
    checks.append({'declaration':name,'axioms':sorted(got)})
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):
    checks.append({'declaration':name,'axioms':[]})
assert len(checks)==22,checks
pending=[ROOT/str(DRIVER),ROOT/(MODULE.replace('.','/')+'.lean')]
seen=set()
while pending:
    path=pending.pop()
    if path in seen:continue
    seen.add(path)
    for imp in re.findall(r'^import\s+(\S+)',path.read_text(),re.M):
        q=ROOT/(imp.replace('.','/')+'.lean')
        if q.is_file():pending.append(q)
spec=importlib.util.spec_from_file_location('project_source_verifier',ROOT/'scripts/verify.py')
verifier=importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
for source in seen:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',verifier.uncomment(source.read_text())),source
seen|={ROOT/'lean-toolchain',ROOT/'lake-manifest.json'}
receipt={'status':'PASS','scope':'Actual arbitrary selected-arity k configurations on Fin(m+k), with selectedLabels literally smallRankGaps sigma k. Selected and tail embeddings have exact selected/complement ranges and cards k,m. Actual graph deletion costs at most k*(N-1), with a natural-subtraction form for all sizes and real-subtraction form when N>=1. Independent full/tail/rank transport and fixed-outer uniform averaging are genuine finite equivalences, including empty selected and tail blocks. No structural matching hypothesis or network lower-bound conclusion is built into these definitions.',
'build_module':MODULE,'exact_driver':str(DRIVER),'axiom_checks':checks,
'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)},
'exact_log_sha256':hashlib.sha256(log.encode()).hexdigest()}
(HERE/f'{PREFIX}_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','axiom_checks':len(checks),'project_source_closure':len(seen)},indent=2))
