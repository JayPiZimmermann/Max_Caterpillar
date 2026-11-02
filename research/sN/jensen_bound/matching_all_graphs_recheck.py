#!/usr/bin/env python3
"""Audit the zero-edge completion of the actual matching estimates."""
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
cached='--cached' in sys.argv
commands=[
 ('module_build',(['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1','-o','.lake/build/lib/MaxCaterpillar/Frontier/RandomRestriction/MatchingSizeBias/AllGraphs.olean','MaxCaterpillar/Frontier/RandomRestriction/MatchingSizeBias/AllGraphs.lean'] if cached else ['scripts/lean_lock.sh','lake','build','MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.AllGraphs'])),
 ('exact',['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1','verification/frontier/MatchingSizeBiasAllGraphsCheck.lean']),
]
checks=[]
for tag,command in commands:
 result=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/f'matching_all_graphs_{tag}.log').write_text(result.stdout)
 (OUT/f'matching_all_graphs_{tag}.exit').write_text(str(result.returncode)+'\n')
 checks.append({'command':command,'exit_code':result.returncode,'log':str((OUT/f'matching_all_graphs_{tag}.log').relative_to(ROOT))})
 if result.returncode:
  print(result.stdout)
  break
pending=['MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.AllGraphs']
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
for name in ['verification/frontier/MatchingSizeBiasAllGraphsCheck.lean','research/sN/jensen_bound/matching_all_graphs_recheck.py','research/sN/zulip_three/lean_small_pool.py','scripts/lean_lock.sh','lake-manifest.json','lean-toolchain']:
 path=ROOT/name
 closure[name]=sha256(path.read_bytes()).hexdigest()
for name in closure:
 if name.endswith('.lean'):
  for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b',mod.uncomment((ROOT/name).read_text())):
   forbidden.append({'file':name,'construct':match.group()})
axiom_checks=[]
if len(checks)==2 and checks[-1]['exit_code']==0:
 for decl,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(OUT/'matching_all_graphs_exact.log').read_text(),re.S):
  axiom_checks.append({'declaration':decl,'axioms':sorted(a.strip() for a in axes.split(',') if a.strip())})
stale=[]
artifacts={}
for name in closure:
 if name.startswith('MaxCaterpillar/') and name.endswith('.lean'):
  art=ROOT/'.lake/build/lib'/Path(name).with_suffix('.olean')
  if not art.is_file() or art.stat().st_mtime_ns < (ROOT/name).stat().st_mtime_ns:
   stale.append(name)
  elif art.is_file():
   artifacts[str(art.relative_to(ROOT))]=sha256(art.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
axes_ok=len(axiom_checks)==5 and all(set(a['axioms'])<=allowed for a in axiom_checks)
receipt={
 'status':'PASS' if len(checks)==2 and all(c['exit_code']==0 for c in checks) and not forbidden and axes_ok and not stale else 'FAIL',
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),
 'receipt_kind':('scoped current owned-kernel-artifact exact-type and axiom audit' if cached else 'scoped canonical rebuilt working-tree exact-type and axiom audit'),
 'result':'The actual ordinary-permutation matching moment and explicitly weighted400/K^2 expression satisfy their bounds for every finite simple graph, including zero edges. Empty graphs have matchingCount identically0 and moment exactly1; no normalized size-bias coupling on the empty dart sample is asserted.',
 'scope':{'random_object':'ordinary uniform vertex permutation','graph':'all finite simple graphs, including zero edges','selected_positions':'fixed injective Fin K times Fin2 map','weighted_hypotheses':'m>=400,0<Kcutoff<=m/100,eta>=0,J>=Kcutoff/2,eta-5(m+4)<=|E(H)|'},
 'not_claimed':['No nonempty normalized dart coupling is claimed for the zero-edge graph','The400bound concerns the displayed weighted moment, not an arbitrary raw moment','This package alone is not a complete neural-network lower-bound assembly'],
 'semantic_checks':[
  'The all-graphs headlines have no positive graph-edge-cardinality premise',
  'An actual adjacency would yield a dart and contradict zero edge cardinality',
  'The empty-graph count is proved identically0 for every permutation',
  'The ordinary uniform-permutation moment is proved exactly1 for every theta in the empty case',
  'Nonempty cases use the frozen verified forcing/identity/damage/analytic route',
  'The empty-case edge-deletion premise bounds eta, making the shifted exponential at least1',
  'The same verified scalar400 bound applies after multiplying the nonnegative weight',
  'A concrete injective Fin1 times Fin2 position model verifies the empty-graph boundary',
  'All original c3 production files and their source-bound receipt are preserved unchanged',
 ],
 'stale_or_missing_project_artifacts':stale,'project_artifact_sha256':dict(sorted(artifacts.items())),
 'commands':checks,'axiom_checks':axiom_checks,'forbidden_constructs':forbidden,
 'project_source_closure_files':sum(n.endswith('.lean') for n in closure),
 'source_sha256':dict(sorted(closure.items())),
 'log_sha256':{tag:sha256((OUT/f'matching_all_graphs_{tag}.log').read_bytes()).hexdigest() for tag,_ in commands if (OUT/f'matching_all_graphs_{tag}.log').exists()},
}
(OUT/'matching_all_graphs_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','project_source_closure_files','commands','forbidden_constructs']},indent=2))
sys.exit(0 if receipt['status']=='PASS' else 1)
