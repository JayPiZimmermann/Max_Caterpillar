"""Recheck actual network chart connectedness and genuine quotient coverage."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'research/sN/zulip_three'
MODULES=['MaxCaterpillar.Fiber.Count65.SectorComponents','MaxCaterpillar.Fiber.Count65.Mixed.QuotientCharts']
DRIVER='verification/fiber/Count65MixedQuotientChartsCheck.lean'
NAMES=['MaxCaterpillar.Fiber.Count65.MixedSectorComponents.isPathConnected_actualChartA',
 'MaxCaterpillar.Fiber.Count65.MixedSectorComponents.isPathConnected_actualChartB']+[
 'MaxCaterpillar.Fiber.Count65.MixedQuotientCharts.'+n for n in ['isPathConnected_quotientChartA',
 'isPathConnected_quotientChartB','classA_quotient_covered','classB_quotient_covered','zeroBias_quotient_coverage']]
def run(args,tag):
 p=subprocess.run([sys.executable,str(OUT/'lean_small_pool.py'),*args],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(tag+'.log')).write_text(p.stdout);(OUT/(tag+'.exit')).write_text(str(p.returncode)+'\n')
 if p.returncode:raise SystemExit(p.stdout)
 return p.stdout

def main():
 for base in ['count65_actual_mixed_receipt.json','count65_actual_mixed_chart_receipt.json']:
  receipt=json.loads((OUT/base).read_text());assert receipt['status']=='PASS'
  for name,h in receipt['source_sha256'].items():
   if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h:raise SystemExit('Base source changed: '+name)
 spec=importlib.util.spec_from_file_location('project_verify',ROOT/'scripts/verify.py')
 verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
 for module in MODULES:
  source=module.replace('.','/')+'.lean';target=ROOT/'.lake/build/lib'/source.replace('.lean','.olean')
  run(['lake','env','lean','-j1','-o',str(target),source],'count65_mixed_quotient_receipt_'+module.rsplit('.',1)[1])
 output=run(['lake','env','lean','-j1',DRIVER],'count65_mixed_quotient_charts_exact')
 axes={n:set(x.strip() for x in a.split(',') if x.strip()) for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)}
 for n in NAMES:
  if n not in axes or not axes[n]<={'propext','Classical.choice','Quot.sound'}:raise SystemExit('Bad axioms: '+n)
 seen=set();todo=[ROOT/DRIVER]+[ROOT/(m.replace('.','/')+'.lean') for m in MODULES]
 while todo:
  p=todo.pop()
  if p in seen:continue
  seen.add(p);source=verify.uncomment(p.read_text())
  if re.search(r'\b(sorry|admit|axiom|native_decide)\b',source):raise SystemExit('Forbidden construct: '+str(p))
  for line in source.splitlines():
   fields=line.split()
   if fields and fields[0]=='import':
    for module in fields[1:]:
     q=ROOT/(module.replace('.','/')+'.lean')
     if q.is_file():todo.append(q)
 seen.update([ROOT/'lean-toolchain',ROOT/'lake-manifest.json',ROOT/'scripts/verify.py',Path(__file__).resolve(),
              OUT/'count65_actual_mixed_receipt.json',OUT/'count65_actual_mixed_chart_receipt.json'])
 receipt={'status':'PASS','checked_at_utc':datetime.now(timezone.utc).isoformat(),'scope':'Path-connected actual mixed chart images and unconditional genuine zero-bias quotient coverage; no global component-count assertion.',
  'modules':MODULES,'driver':DRIVER,'module_build_exit':0,'exact_check_exit':0,'axioms':{n:sorted(axes[n]) for n in NAMES},
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}}
 dest=OUT/'count65_mixed_quotient_charts_receipt.json';dest.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'status':'PASS','hashes':len(seen),'axiom_checks':len(NAMES),'receipt':str(dest.relative_to(ROOT))}))
if __name__=='__main__':main()
