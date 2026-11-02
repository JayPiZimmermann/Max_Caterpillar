#!/usr/bin/env python3
"""Audit actual selected-graph events, structural intersection, and deletion."""
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
 ('module_build',(['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1','-o','.lake/build/lib/MaxCaterpillar/Frontier/RandomRestriction/GraphRestriction.olean','MaxCaterpillar/Frontier/RandomRestriction/GraphRestriction.lean'] if cached else ['scripts/lean_lock.sh','lake','build','MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction'])),
 ('exact',['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1','verification/frontier/GraphRestrictionCheck.lean']),
]
checks=[]
for tag,command in commands:
 result=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/f'graph_restriction_{tag}.log').write_text(result.stdout)
 (OUT/f'graph_restriction_{tag}.exit').write_text(str(result.returncode)+'\n')
 checks.append({'command':command,'exit_code':result.returncode,'log':str((OUT/f'graph_restriction_{tag}.log').relative_to(ROOT))})
 if result.returncode:
  print(result.stdout)
  break
pending=['MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction']
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
for name in ['verification/frontier/GraphRestrictionCheck.lean','research/sN/jensen_bound/graph_restriction_recheck.py','research/sN/zulip_three/lean_small_pool.py','scripts/lean_lock.sh','lake-manifest.json','lean-toolchain']:
 path=ROOT/name
 closure[name]=sha256(path.read_bytes()).hexdigest()
for name in closure:
 if name.endswith('.lean'):
  for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b',mod.uncomment((ROOT/name).read_text())):
   forbidden.append({'file':name,'construct':match.group()})
axiom_checks=[]
if len(checks)==2 and checks[-1]['exit_code']==0:
 for decl,axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",(OUT/'graph_restriction_exact.log').read_text(),re.S):
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
axes_ok=len(axiom_checks)==15 and all(set(a['axioms'])<=allowed for a in axiom_checks)
receipt={
 'status':'PASS' if len(checks)==2 and all(c['exit_code']==0 for c in checks) and not forbidden and axes_ok and not stale else 'FAIL',
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),
 'receipt_kind':('scoped current owned-kernel-artifact exact-type and axiom audit' if cached else 'scoped canonical rebuilt working-tree exact-type and axiom audit'),
 'result':'For a genuine uniform label-to-position permutation, the five selected labels contain two disjoint ordinary graph edges with probability at most60eta^2/(N)_4. The same event is exactly failure of PairwiseIntersectingEdges for the actual five-label comap. Its probability is at most60eta^2/m^4 for N=m+5,m>0. The actual complementary tail graph from the same permutation has at least eta-5(m+4) edges.',
 'scope':{'graph':'arbitrary finite simple graph, including empty graphs','selected_set':'actual GoodEvent.smallRankGaps permutation5','permutation_convention':'label maps to position; selected/tail embeddings use inverse permutation','event':'actual two disjoint ordinary graph edges with all four endpoints selected','deletion':'actual complement induced graph, including its canonical Fin m relabeling'},
 'not_claimed':['No independence between selected-edge events is assumed','This graph package does not itself prove a complete neural-network counting inequality'],
 'semantic_checks':[
  'Four fixed distinct labels are selected with the exact actual fraction120/(N)_4',
  'Graph edges are ordinary unordered Sym2 values in SimpleGraph.edgeFinset',
  'The literal existential bad event is covered by unordered two-edge subsets with disjoint endpoints',
  'There are at most choose(eta,2) witnesses; their four endpoint sets have cardinality4',
  'The finite union bound gives120choose(eta,2)/(N)_4 and hence60eta^2/(N)_4',
  'Failure of the existing PairwiseIntersectingEdges condition is proved equivalent to the actual selected-edge event',
  'The selected graph and complementary tail graph are actual comaps of the same original graph and permutation',
  'Exact inverse-permutation range lemmas identify selected and complementary vertices',
  'Deleted edges are bounded by the sum of incident degrees at deleted vertices',
  'Retained edge cardinality is proved equal to actual induced/comap graph edge cardinality',
  'The real eta-5(m+4) lower bound is derived from a Nat addition inequality, including negative values',
  'Separate child exact checks include five/six-vertex probability sanity cases, a genuine two-disjoint-edge graph, inverse-orientation cycle, and empty-tail boundary',
 ],
 'stale_or_missing_project_artifacts':stale,'project_artifact_sha256':dict(sorted(artifacts.items())),
 'commands':checks,'axiom_checks':axiom_checks,'forbidden_constructs':forbidden,
 'project_source_closure_files':sum(n.endswith('.lean') for n in closure),
 'source_sha256':dict(sorted(closure.items())),
 'log_sha256':{tag:sha256((OUT/f'graph_restriction_{tag}.log').read_bytes()).hexdigest() for tag,_ in commands if (OUT/f'graph_restriction_{tag}.log').exists()},
}
(OUT/'graph_restriction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','project_source_closure_files','commands','forbidden_constructs']},indent=2))
sys.exit(0 if receipt['status']=='PASS' else 1)
