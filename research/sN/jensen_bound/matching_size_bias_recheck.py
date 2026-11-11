#!/usr/bin/env python3
"""Audit actual partial-matching forcing, size bias, and the geometric/counting bounds."""
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
 ('module_build',(['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1','-o','.lake/build/lib/MaxCaterpillar/Frontier/RandomRestriction/MatchingSizeBias.olean','MaxCaterpillar/Frontier/RandomRestriction/MatchingSizeBias.lean'] if cached else ['scripts/lean_lock.sh','lake','build','MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias'])),
 ('exact',['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1','verification/frontier/MatchingSizeBiasCheck.lean']),
]
checks=[]
for tag,command in commands:
 result=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/f'matching_size_bias_{tag}.log').write_text(result.stdout)
 (OUT/f'matching_size_bias_{tag}.exit').write_text(str(result.returncode)+'\n')
 checks.append({'command':command,'exit_code':result.returncode,'log':str((OUT/f'matching_size_bias_{tag}.log').relative_to(ROOT))})
 if result.returncode:
  print(result.stdout)
  break
pending=['MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias']
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
for name in ['verification/frontier/MatchingSizeBiasCheck.lean','research/sN/jensen_bound/matching_size_bias_recheck.py','research/sN/zulip_three/lean_small_pool.py','scripts/lean_lock.sh','lake-manifest.json','lean-toolchain']:
 path=ROOT/name
 closure[name]=sha256(path.read_bytes()).hexdigest()
for name in closure:
 if name.endswith('.lean'):
  for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b',mod.uncomment((ROOT/name).read_text())):
   forbidden.append({'file':name,'construct':match.group()})
axiom_checks=[]
if len(checks)==2 and checks[-1]['exit_code']==0:
 for decl,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(OUT/'matching_size_bias_exact.log').read_text(),re.S):
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
axes_ok=len(axiom_checks)==13 and all(set(a['axioms'])<=allowed for a in axiom_checks)
receipt={
 'status':'PASS' if len(checks)==2 and all(c['exit_code']==0 for c in checks) and not forbidden and axes_ok and not stale else 'FAIL',
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),
 'receipt_kind':('scoped current owned-kernel-artifact exact-type and axiom audit' if cached else 'scoped canonical rebuilt working-tree exact-type and axiom audit'),
 'result':'For the actual number X of graph edges among fixed disjoint position pairs under an ordinary uniform vertex permutation, E theta^X is at most exp(-(2K|E|/(m(m-1)))*(1-theta^3)/3), for0<theta<=1,positiveKandedgecount. The actual forcing experiment satisfies the normalized size-bias identity and Y<=X+3. Its explicitly weighted counting expression is at most400/Kcutoff^2 under the recorded application hypotheses.',
 'scope':{'random_object':'ordinary uniform permutation of Fin m','graph':'arbitrary nonempty finite simple graph','selected_positions':'fixed injective Fin K times Fin2 map into Fin m','theta':'0<theta<=1','mean':'2K|E(H)|/[m(m-1)]','size_bias_coupling':'actual two-position-transposition forcing with constant conditional preimage count m(m-1)'},
 'not_claimed':['The plain unweighted moment need not be at most400/K^2 for arbitrary sparse graphs','The weighted400 theorem explicitly retains the edge-deletion, pair-count, arity and cutoff hypotheses','The c2 matching-level repair remains an unformalized future alternative','No complete neural-network lower bound follows from this probability package alone'],
 'semantic_checks':[
  'The variable matchingCount counts actual SimpleGraph adjacency at permuted selected endpoints',
  'Oriented edges are canonical SimpleGraph.Dart values and their cardinality is proved twice the undirected edge count',
  'The forcing map consists of two explicit position transpositions on ordinary permutations',
  'An actual inverse proves the forcing equivalence and the constant conditional fiber cardinality',
  'The finite incidence partition proves the true size-bias identity for every real test function',
  'Uniform joint weights are normalized and their original-permutation marginal is proved for every test function',
  'Endpoint injectivity proves at most three selected pair indicators can change',
  'Neither a coupling identity nor a damage bound is a hypothesis of the headline',
  'The analytic estimate is applied with the correct negative log-theta sign',
  'The weighted400 theorem applies the exact actual half-moment bound before the verified scalar optimization',
  'A separate child exact-type check supplies the nonempty m2,K1,complete-graph witness with X=Y=mu=1',
 ],
 'stale_or_missing_project_artifacts':stale,'project_artifact_sha256':dict(sorted(artifacts.items())),
 'commands':checks,'axiom_checks':axiom_checks,'forbidden_constructs':forbidden,
 'project_source_closure_files':sum(n.endswith('.lean') for n in closure),
 'source_sha256':dict(sorted(closure.items())),
 'log_sha256':{tag:sha256((OUT/f'matching_size_bias_{tag}.log').read_bytes()).hexdigest() for tag,_ in commands if (OUT/f'matching_size_bias_{tag}.log').exists()},
}
(OUT/'matching_size_bias_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','project_source_closure_files','commands','forbidden_constructs']},indent=2))
sys.exit(0 if receipt['status']=='PASS' else 1)
