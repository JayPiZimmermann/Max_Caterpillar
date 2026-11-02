"""Source-bound check of actual mixed physical label continuity and symmetry."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/sN/zulip_three'
MODULES=['MaxCaterpillar.Fiber.Count65.FiniteClosedPartition',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabels',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsExhaustion',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsSeparation',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsContinuity',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsNormalization',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsSymmetry',
 'MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsOrbit']
DRIVER='verification/fiber/Count65ActualMixedLabelsCheck.lean'
PREFIX='MaxCaterpillar.Fiber.Count65.ActualMixedLabels.'
NAMES=[PREFIX+n for n in ['physicalClasses_exhaustive','physicalClass_unique',
 'continuous_actualLabel','continuous_componentLabel','continuous_rawComponentLabel',
 'componentLabel_permutePhysical','normalizePhysical_sameQuotient']]+['actualRawWitness']

def run(args,tag):
 p=subprocess.run([sys.executable,str(OUT/'lean_small_pool.py'),*args],cwd=ROOT,
                  text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(tag+'.log')).write_text(p.stdout);(OUT/(tag+'.exit')).write_text(str(p.returncode)+'\n')
 if p.returncode:raise SystemExit(p.stdout)
 return p.stdout

def main():
 spec=importlib.util.spec_from_file_location('project_verify',ROOT/'scripts/verify.py')
 verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
 for module in MODULES:
  source=module.replace('.','/')+'.lean';target=ROOT/'.lake/build/lib'/source.replace('.lean','.olean')
  target.parent.mkdir(parents=True,exist_ok=True)
  run(['lake','env','lean','-j1','-o',str(target),source],
      'count65_actual_mixed_receipt_'+module.rsplit('.',1)[1])
 output=run(['lake','env','lean','-j1',DRIVER],'count65_actual_mixed_labels_exact')
 axes={n:set(x.strip() for x in a.split(',') if x.strip()) for n,a in
       re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)}
 for name in NAMES:
  if name not in axes or not axes[name]<={'propext','Classical.choice','Quot.sound'}:
   raise SystemExit('Bad axiom audit: '+name+': '+str(axes.get(name)))
 seen=set();todo=[ROOT/DRIVER]+[ROOT/(m.replace('.','/')+'.lean') for m in MODULES]
 while todo:
  p=todo.pop()
  if p in seen:continue
  seen.add(p);source=verify.uncomment(p.read_text())
  if re.search(r'\b(sorry|admit|axiom|native_decide)\b',source):
   raise SystemExit('Forbidden construct: '+str(p))
  for line in source.splitlines():
   fields=line.split()
   if fields and fields[0]=='import':
    for module in fields[1:]:
     q=ROOT/(module.replace('.','/')+'.lean')
     if q.is_file():todo.append(q)
 seen.update([ROOT/'lean-toolchain',ROOT/'lake-manifest.json',ROOT/'scripts/verify.py',
              Path(__file__).resolve()])
 receipt={'status':'PASS','checked_at_utc':datetime.now(timezone.utc).isoformat(),
  'scope':'Actual canonical mixed first-row physical networks: exhaustive unique closed partition, continuous finite labels before and after output normalization, actual second-row permutation invariance. Does not assert full sector or global component count.',
  'module_build_exit':0,'exact_check_exit':0,'modules':MODULES,'driver':DRIVER,
  'axioms':{n:sorted(axes[n]) for n in NAMES},
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}}
 dest=OUT/'count65_actual_mixed_receipt.json';dest.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'status':'PASS','hashes':len(seen),'axiom_checks':len(NAMES),'receipt':str(dest.relative_to(ROOT))}))
if __name__=='__main__':main()
