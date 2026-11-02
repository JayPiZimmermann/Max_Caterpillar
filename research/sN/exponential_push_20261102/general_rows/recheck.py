"""Scoped isolated-research gate; no root imports or publication are claimed."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,datetime
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
LEAN=OUT/'AdaptiveOffset.lean'
ALLOWED={'propext','Classical.choice','Quot.sound'}
spec=importlib.util.spec_from_file_location('verify',ROOT/'scripts/verify.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
def closure():
 seen=set();pending=[LEAN.relative_to(ROOT).as_posix()]
 while pending:
  rel=pending.pop()
  if rel in seen:continue
  seen.add(rel)
  clean=verify.uncomment((ROOT/rel).read_text())
  for imports in re.findall(r'^import[ \t]+([^\n]+)',clean,re.M):
   for module in imports.split():
    if module.startswith(('MaxCaterpillar','MaxNN')):pending.append(module.replace('.','/')+'.lean')
 return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()for p in sorted(seen)}
def run(args,name):
 result=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(name+'.log')).write_text(result.stdout);(OUT/(name+'.exit')).write_text(str(result.returncode)+'\n')
 if result.returncode:raise RuntimeError(result.stdout)
 return result.stdout
before=closure()
clean=verify.uncomment(LEAN.read_text())
assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b|Lean\.ofReduceBool',clean)
stdout=run(['python3','research/sN/zulip_three/lean_small_pool.py','lake','env','lean','-j1',str(LEAN.relative_to(ROOT))],'adaptive_offset')
audits=[]
for name,entries in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",stdout,re.S):
 axioms=[x.strip()for x in entries.split(',')if x.strip()]
 assert set(axioms)<=ALLOWED,(name,axioms)
 audits.append({'declaration':name,'axioms':axioms})
assert len(audits)==10,len(audits)
assert closure()==before,'Project source changed during gate'
for script in ('sharp_cubic_control.py','selector_control.py','selector_probability_check.py'):
 run(['python3',str((OUT/script).relative_to(ROOT))],script.removesuffix('.py'))
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Isolated actual adaptive-offset Lean counterexample plus exact finite selector/Good/Q/probability controls. The logarithmic asymptotic is a mathematical proof and independent audit, not a Lean theorem.',
 'not_claimed':'No SCprime2 certificate verification, no exact MAX-network counterexample, no nonzero certificate score, no unconditional width lower bound, no production root integration.',
 'lean_axiom_checks':audits,'lean_project_source_hashes':before,'project_source_closure_stable':True,
 'artifact_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted(OUT.iterdir())if p.suffix in('.lean','.py','.md','.json')and p.name!='receipt.json'},
 'reproduce':'python3 research/sN/exponential_push_20261102/general_rows/recheck.py'}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','axiom_checks':len(audits),'project_sources':len(before)}))
