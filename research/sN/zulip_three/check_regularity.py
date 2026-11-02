"""Build and exact-check smooth regularity of the full bias-free Max4 fiber.

Run under the shared Lean lock. This creates a content-bound workspace receipt;
a publication gate should re-run it against the final committed source closure.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
MODULE='MaxCaterpillar.Fiber.GatingAbstractions.RegularityChart'
DRIVER=Path('verification/fiber/GatingRegularityCheck.lean')
PREFIX='regularity'
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
required={
 'MaxCaterpillar.Fiber.GatingAbstractions.smooth_regular_family_one',
 'MaxCaterpillar.Fiber.GatingAbstractions.smooth_regular_family_two',
 'MaxCaterpillar.Fiber.GatingAbstractions.regular_family_one',
 'MaxCaterpillar.Fiber.GatingAbstractions.regular_family_two',
}
assert required<={x['declaration'] for x in checks},checks
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
receipt={'status':'PASS',
'scope':'Ambient smooth regularity of the entire all-real-input exact fiber of bias-free physical Max4 (6,3) networks at canonical family(1) and family(2). All 45 physical weights vary; the fiber is locally a 17-dimensional coordinate plane of codimension 28.',
'evidence_kind':'Content-bound workspace receipt; final clean-commit publication gate remains a separate promotion step.',
'build_module':MODULE,'exact_driver':str(DRIVER),'axiom_checks':checks,
'claims':[
 {'declaration':'MaxCaterpillar.Fiber.GatingAbstractions.smooth_regular_family_'+word,
  'expected_type':'HasSmoothRegularFiberChartAt (V := Fin 28 → ℝ) (W := Fin 17 → ℝ) {p : Fin 45 → ℝ | ∀ x : Point 4, (fromRaw p).eval x = Maximum 4 x} (toRaw (family '+str(c)+'))'}
 for word,c in [('one',1),('two',2)]],
'semantic_checks':['Expanded chart definition includes invertible strict derivative, forward smoothness, inverse smoothness, and equality with the whole set on the ambient open source.',
 'Literal expected types quantify over all real inputs and all 45 raw weight entries.',
 'Raw coordinates are homeomorphic to the full zero-bias physical Network model and its exact fiber.'],
'proof_method':'28 strict-gate evaluations plus 17 physical weight coordinates have an invertible derivative. A continuous locally exact reconstruction is a right inverse to the 17 coordinates. Ambient inverse-function injectivity proves the entire exact fiber locally equals the regular finite level set.',
'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)},
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'exact_log_sha256':hashlib.sha256(log.encode()).hexdigest()}
(HERE/f'{PREFIX}_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','axiom_checks':len(checks),'project_source_closure':len(seen)},indent=2))
