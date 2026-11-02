"""Exact final count65 source-bound verification; no Lean source generation."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'research/sN/zulip_three'
MODULES=['MaxCaterpillar.Fiber.Count65.GlobalComponents','MaxCaterpillar.Fiber.Count65']
DRIVER='verification/fiber/Count65Check.lean'
BASES=['count65_paired_connected_receipt.json','count65_mixed_full_sector_receipt.json',
       'count65_star_full_sector_receipt.json','atleast65_receipt.json']
NAMES=['MaxCaterpillar.Fiber.max4_6_5_has_65_components',
 'MaxCaterpillar.Fiber.max4_6_5_component_count_eq_65',
 'MaxCaterpillar.Fiber.Count65.zeroBiasComponentsEquiv65',
 'MaxCaterpillar.Fiber.Count65.fullComponentsEquiv65',
 'MaxCaterpillar.Fiber.Count65.Paired.isPathConnected_quotientSector',
 'MaxCaterpillar.Fiber.Count65.MixedFullSectorComponents.mixed_actual_sector_has_32_components',
 'MaxCaterpillar.Fiber.Count65.StarFullSectorComponents.star_actual_sector_has_32_components',
 'MaxCaterpillar.Fiber.Count65.globalLabel_surjective',
 'MaxCaterpillar.Fiber.zeroBiasQuotientConnectedComponentsEquiv']

def run(args,tag):
 launcher=([str(ROOT/'scripts/lean_lock.sh')] if '--lake' in sys.argv else
           [sys.executable,str(OUT/'lean_small_pool.py')])
 p=subprocess.run([*launcher,*args],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(tag+'.log')).write_text(p.stdout);(OUT/(tag+'.exit')).write_text(str(p.returncode)+'\n')
 if p.returncode:raise SystemExit(p.stdout)
 return p.stdout

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 for name in BASES:
  d=json.loads((OUT/name).read_text())
  if d['status']!='PASS':raise SystemExit('Non-PASS factor receipt: '+name)
  for relative,h in d['source_sha256'].items():
   if sha(ROOT/relative)!=h:raise SystemExit('Stale factor source: '+relative)
 spec=importlib.util.spec_from_file_location('project_verify',ROOT/'scripts/verify.py')
 verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
 seen=set();todo=[ROOT/DRIVER]+[ROOT/(m.replace('.','/')+'.lean') for m in MODULES]
 while todo:
  p=todo.pop()
  if p in seen:continue
  seen.add(p);source=verify.uncomment(p.read_text())
  if re.search(r'\b(sorry|admit|axiom|native_decide)\b',source):raise SystemExit('Forbidden proof construct: '+str(p))
  for line in source.splitlines():
   fields=line.split()
   if fields and fields[0]=='import':
    for module in fields[1:]:
     q=ROOT/(module.replace('.','/')+'.lean')
     if q.is_file():todo.append(q)
 seen.update([ROOT/'lean-toolchain',ROOT/'lake-manifest.json',ROOT/'scripts/verify.py',
              Path(__file__).resolve(),*[OUT/n for n in BASES]])
 before={str(p.relative_to(ROOT)):sha(p) for p in sorted(seen)}
 if '--lake' in sys.argv:
  run(['lake','build',*MODULES],'count65_final_modules')
 else:
  for m in MODULES:
   source=m.replace('.','/')+'.lean';target=ROOT/'.lake/build/lib'/source.replace('.lean','.olean')
   target.parent.mkdir(parents=True,exist_ok=True)
   run(['lake','env','lean','-j1','-o',str(target),source],'count65_final_'+m.rsplit('.',1)[1])
 output=run(['lake','env','lean','-j1',DRIVER],'count65_final_exact')
 axes={n:set(x.strip() for x in a.split(',') if x.strip()) for n,a in
       re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)}
 for n in NAMES:
  if n not in axes or not axes[n]<={'propext','Classical.choice','Quot.sound'}:
   raise SystemExit('Bad exact axiom audit: '+n+': '+str(axes.get(n)))
 after={str(p.relative_to(ROOT)):sha(p) for p in sorted(seen)}
 if after!=before:raise SystemExit('A proof source changed during verification; rerun.')
 receipt={'status':'PASS','checked_at_utc':datetime.now(timezone.utc).isoformat(),
  'theorem':'MaxCaterpillar.Fiber.max4_6_5_has_65_components',
  'scope':'Exactly65 connected components of the complete real all-input Max4(6,5) exact fiber modulo only positive first/second hidden rescalings, hidden permutations, and input permutations; arbitrary biases allowed.',
  'headline_hypotheses':[],'factor_counts':{'paired':1,'mixed':32,'star':32},
  'bias_reduction':'Verified component equivalence on the genuine physical quotient',
  'verification':'Independently spelled actual Network/all-real-input carrier and EqvGen SymmetryStep relation; fresh expected-type driver; transitive theorem axiom and project source-closure audits',
  'modules':MODULES,'driver':DRIVER,'module_build_exit':0,'exact_check_exit':0,
  'build_mode':'lake build under global lock' if '--lake' in sys.argv else 'authorized owned-module small-pool build over source-bound verified factors',
  'factor_receipts':BASES,'axioms':{n:sorted(axes[n]) for n in NAMES},'source_sha256':after}
 dest=OUT/'count65_receipt.json';dest.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'status':'PASS','source_hashes':len(after),'axiom_audits':len(NAMES),
                   'theorem':receipt['theorem'],'receipt':str(dest.relative_to(ROOT))}))
if __name__=='__main__':main()
