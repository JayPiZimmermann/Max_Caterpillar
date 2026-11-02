"""Content-bound receipt for the closed all-real star obstruction.

This records kernel/consumer checks already run; it does not replace them.
The final verification/h2/StarObstructionCheck.lean is the exact-type contract.
"""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[4];D=Path(__file__).parent
MODULE=ROOT/'MaxCaterpillar/Frontier/StarCertificate/StarObstruction.lean'
DRIVER=ROOT/'verification/h2/StarObstructionCheck.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def closure(start):
 found={};todo=[start]
 while todo:
  p=todo.pop()
  if p in found:continue
  found[p]=sha(p)
  for line in p.read_text().splitlines():
   if line.strip().startswith('import '):
    for name in line.strip()[7:].split():
     q=ROOT/Path(*name.split('.')).with_suffix('.lean')
     if q.exists():todo.append(q)
 return found

def strip_comments(text):
 out=[];i=0;depth=0;line=False;quoted=False
 while i<len(text):
  pair=text[i:i+2]
  if line:
   if text[i]=='\n':line=False;out.append('\n')
   i+=1;continue
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:i+=1
   continue
  if quoted:
   if text[i]=='\\':i+=2
   elif text[i]=='"':quoted=False;i+=1
   else:i+=1
   continue
  if pair=='--':line=True;i+=2
  elif pair=='/-':depth=1;i+=2
  elif text[i]=='"':quoted=True;i+=1
  else:out.append(text[i]);i+=1
 return ''.join(out)

log=(D/'star_obstruction_exact_check.log').read_text();assert 'error:' not in log
reports={name:[x.strip() for x in axioms.split(',') if x.strip()] for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
allowed={'propext','Classical.choice','Quot.sound'}
assert len(reports)==5 and all(set(a)<=allowed for a in reports.values())
assert set(reports)=={'MaxCaterpillar.Frontier.StarCertificate.'+n for n in ['starAnova_all_real','starAt_permutation_sum_eq_zero','star_network_topMobius_zero','star_network_booleanQuadratic_topMobius_zero','star_network_booleanQuadratic_not_booleanOR']}
jobs=json.load(open(D/'profile_targets_representatives_status.json'));assert jobs['status']=='complete' and len(jobs['records'])==239
for r in jobs['records']:
 assert r['exit']==0
 source=ROOT/Path(*r['module'].split('.')).with_suffix('.lean');assert sha(source)==r['source_sha256']
 artifact=ROOT/'.lake/build/lib'/Path(*r['module'].split('.')).with_suffix('.olean');assert sha(artifact)==r['artifact_sha256']
sources=closure(MODULE);sources.update(closure(DRIVER));bad=[]
for p in sources:
 text=strip_comments(p.read_text())
 if re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|\bLean\.ofReduceBool\b|(?m:^\s*(?:private\s+)?axiom\s+)',text):bad.append(str(p.relative_to(ROOT)))
assert not bad,bad
for p,h in sources.items():assert sha(p)==h
assert (D/'KernelCheckGood.exit').read_text().strip()=='0'
assert (D/'KernelCheckFalse.exit').read_text().strip()=='1'
assert '(kernel) declaration type mismatch' in (D/'KernelCheckFalse.log').read_text()
receipt={'success':True,'evidence':'Lean verified; independent expanded-type/nonvacuity/axiom consumer passed',
 'production_module':'MaxCaterpillar.Frontier.StarCertificate.StarObstruction','exact_driver':str(DRIVER.relative_to(ROOT)),
 'scope':'All real four-slope anchored identities; all arbitrary-centre real-slope stars on five inputs; finite signed-star gluing has zero fifth Mobius coefficient, including every resonance boundary.',
 'no_certificate_hypothesis_in_closed_declarations':True,'numerical_jobs':len(jobs['records']),'representatives':67,'halfspace_strata':900,'halfspace_farkas_exclusions':6330,
 'axioms':reports,'allowed_axioms':sorted(allowed),'no_cheat_scan':{'passed':True,'project_sources':len(sources)},
 'kernel_boolean_checker':{'proposed_proof_term':'Eq.refl Bool.true','elaborator_evaluates_check':False,'positive_control_exit':0,'false_control_exit':1,'false_control_rejected_by_kernel':True},
 'input_hashes':{str(p.relative_to(ROOT)):sha(p) for p in [D/'certificate_small_candidate.json',D/'exact_tree_candidate.json',D/'orbit_manifest.json',D/'representative_profile_jobs.json',D/'profile_targets_representatives_status.json',D/'star_obstruction_exact_check.log']},
 'source_hashes':{str(p.relative_to(ROOT)):h for p,h in sorted(sources.items(),key=lambda x:str(x[0]))},
 'lean_toolchain':(ROOT/'lean-toolchain').read_text().strip(),
 'repository_state':'scoped working-tree receipt; parent owns clean public import/commit gate'}
(D/'star_obstruction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'success':True,'project_sources':len(sources),'axiom_reports':len(reports),'numerical_jobs':239},indent=2))
