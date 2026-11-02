#!/usr/bin/env python3
"""Rebuild the actual full-parameter empirical regularity theorem and audit it."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('max_verify_source_parser',ROOT/'scripts/verify.py')
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
commands=[
 ('module_build',['flock','/tmp/max_caterpillar_zulip_three_lean.lock','lake','build','MaxCaterpillar.Fiber.GatingAbstractions.EmpiricalRegularity']),
 ('exact',['flock','/tmp/max_caterpillar_zulip_three_lean.lock','lake','env','lean','-j1','verification/fiber/GatingEmpiricalCheck.lean']),
]
checks=[]
for tag,command in commands:
 result=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/f'empirical_{tag}.log').write_text(result.stdout)
 (OUT/f'empirical_{tag}.exit').write_text(str(result.returncode)+'\n')
 checks.append({'command':command,'exit_code':result.returncode,'log':str((OUT/f'empirical_{tag}.log').relative_to(ROOT))})
 if result.returncode:
  print(result.stdout)
  break
pending=['MaxCaterpillar.Fiber.GatingAbstractions.EmpiricalRegularity']
closure={}
forbidden=[]
while pending:
 name=pending.pop()
 path=ROOT/Path(*name.split('.')).with_suffix('.lean')
 if not path.is_file() or str(path.relative_to(ROOT)) in closure:
  continue
 closure[str(path.relative_to(ROOT))]=sha256(path.read_bytes()).hexdigest()
 clean=mod.uncomment(path.read_text())
 for line in clean.splitlines():
  if line.startswith('import '): pending.extend(line[7:].split())
for name in ['verification/fiber/GatingEmpiricalCheck.lean','research/sN/zulip_three/empirical_recheck.py','lake-manifest.json','lean-toolchain']:
 path=ROOT/name
 closure[name]=sha256(path.read_bytes()).hexdigest()
for name in closure:
 if name.endswith('.lean'):
  for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b',mod.uncomment((ROOT/name).read_text())):
   forbidden.append({'file':name,'construct':match.group()})
axiom_checks=[]
if len(checks)==2 and checks[-1]['exit_code']==0:
 for decl,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(OUT/'empirical_exact.log').read_text(),re.S):
  axiom_checks.append({'declaration':decl,'axioms':sorted(a.strip() for a in axes.split(',') if a.strip())})
allowed={'propext','Classical.choice','Quot.sound'}
axes_ok=len(axiom_checks)==6 and all(set(a['axioms'])<=allowed for a in axiom_checks)
receipt={
 'status':'PASS' if len(checks)==2 and all(c['exit_code']==0 for c in checks) and not forbidden and axes_ok else 'FAIL',
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),
 'receipt_kind':'scoped rebuilt working-tree exact-type and axiom audit',
 'result':'For each positive common-offset parameter c, the full 55-dimensional ordinary biased Max4 parameter space has a regular ambient chart for its empirical Max fiber on four fixed inputs, with dimension51. The two representation-merging points c=1,2 have the same complete all-input gate map but incomparable representation partitions and are both regular empirical-fiber points.',
 'scope':{'architecture':[4,6,3,1],'biases':'arbitrary in the ambient empirical fiber','inputs':[[2,1,3,1],[2,1.5,3,1],[2.5,2,3,1],[5,1,3,1]],'targets':[3,3,3,5],'ambient_real_dimension':55,'observation_rank':4,'empirical_fiber_dimension':51},
 'not_claimed':['This is not the 17-dimensional all-input exact zero-bias fiber chart','No new global connected-component count is asserted'],
 'semantic_checks':[
  'ParameterSpace 4 6 3 is the complete product of six real coefficient arrays; no coefficient is fixed',
  'FiniteDimensional.finrank of the parameter space is proved to be55',
  'The four observed inputs are fixed independently of c',
  'The family itself is exact on every real input, while the ambient level set requires equality only on the four declared observations',
  'Strict first/second sample preactivations are proved from actual physical networks',
  'The full Frechet derivative is derived from the actual nested-ReLU Network.eval formula',
  'Four original physical parameter directions produce the displayed four-by-four map',
  'An exact rightinverse proves surjectivity; no numerical determinant evidence is used',
  'The implicit-function theorem constructs an actual ambient PartialHomeomorph with invertible strict derivative straightening the entire empirical level set',
  'A proved bridge identifies that level set with actual Max4 output constraints',
  'Both merge points are regular and their complete gate maps agree, while the two representation partitions are incomparable',
 ],
 'commands':checks,'axiom_checks':axiom_checks,'forbidden_constructs':forbidden,
 'project_source_closure_files':sum(n.endswith('.lean') for n in closure),
 'source_sha256':dict(sorted(closure.items())),
 'log_sha256':{tag:sha256((OUT/f'empirical_{tag}.log').read_bytes()).hexdigest() for tag,_ in commands if (OUT/f'empirical_{tag}.log').exists()},
}
(OUT/'empirical_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','project_source_closure_files','commands','forbidden_constructs']},indent=2))
sys.exit(0 if receipt['status']=='PASS' else 1)
