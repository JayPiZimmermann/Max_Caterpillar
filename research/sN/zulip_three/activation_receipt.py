"""Record the completed scoped activation/intervention Lean verification.

Run the documented Lake build and exact-declaration check before this script.
This checks their exit markers and axiom output, scans owned source files, and
hashes the complete project-source import closure (third-party mathlib is pinned
by lake-manifest.json). It does not treat an old receipt as a new compile.
"""
from pathlib import Path
import hashlib
import json
import re
import importlib.util
from datetime import datetime, timezone

ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/sN/zulip_three'
MODULE=Path('MaxCaterpillar/Fiber/NaturalInterventions.lean')
CHECK=Path('verification/fiber/NaturalInterventionsCheck.lean')
allowed={'propext','Classical.choice','Quot.sound'}
for name in ['activation_build','activation_module','activation_exact']:
    assert (OUT/(name+'.exit')).read_text().strip()=='0', name
log=(OUT/'activation_exact.log').read_text()
assert ': error:' not in log
entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
assert len(entries)==14, len(entries)
audit=[]
for decl,raw in entries:
    axioms={s.strip() for s in raw.split(',') if s.strip()}
    assert axioms<=allowed, (decl,axioms)
    audit.append({'declaration':decl,'axioms':sorted(axioms)})

spec=importlib.util.spec_from_file_location('project_verify',ROOT/'scripts/verify.py')
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
for owned in [MODULE,CHECK]:
    clean=mod.uncomment((ROOT/owned).read_text())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),str(owned)

sources={}
def visit(module):
    p=Path(*module.split('.')).with_suffix('.lean')
    if str(p) in sources or not (ROOT/p).is_file(): return
    content=(ROOT/p).read_bytes()
    sources[str(p)]=hashlib.sha256(content).hexdigest()
    for line in mod.uncomment(content.decode()).splitlines():
        if line.startswith('import '):
            for imported in line[7:].split(): visit(imported)
visit('MaxCaterpillar.Fiber.NaturalInterventions')
for p in [CHECK,Path('lean-toolchain'),Path('lake-manifest.json'),Path('scripts/verify.py'),
          Path('research/sN/zulip_three/activation_receipt.py')]:
    sources[str(p)]=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()

receipt={
 'status':'PASS',
 'checked_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'Explicit ordinary zero-bias minimal-width Max4 (6,3) networks; equality of both complete post-ReLU natural hidden maps on every real input; one-neuron interchange using the same real base and donor gives outputs 0 and 1; an explicit path in the full all-input exact fiber joins the endpoints and keeps both hidden maps fixed.',
 'topology':'The canonical six-array Network parameter topology and ExactFiber subspace topology from MaxCaterpillar/Fiber/Basic.lean.',
 'headline':'MaxCaterpillar.Fiber.NaturalInterventions.connected_natural_activation_counterexample',
 'unconditional_counterexample':'MaxCaterpillar.Fiber.NaturalInterventions.natural_activation_counterexample',
 'path':'MaxCaterpillar.Fiber.NaturalInterventions.exactPath',
 'component_equality':'MaxCaterpillar.Fiber.NaturalInterventions.same_exact_component',
 'base':[0,0,-1,-1],
 'donor':[0,0,0,1],
 'interchanged_neuron_zero_based':4,
 'endpoint_parameter_values':[0,1],
 'interchange_outputs':[0,1],
 'semantic_checks':[
   'Network.firstHidden and Network.secondHidden are direct physical matrix/ReLU formulas.',
   'Network.fromFirstHidden recomputes the physical second layer and affine output.',
   'Network.interchangeFirst uses Function.update on the actual first hidden state with the value from an actual real donor.',
   'Every member net(t) for t>=0 computes Max4 on all real inputs, including switching boundaries.',
   'Both complete post-ReLU hidden maps are independent of t>=0.',
   'The exact path has domain the closed unit interval, with the actual endpoint networks.',
   'Arbitrary-bias Max4 width lower bounds prove the witness widths minimal.'
 ],
 'commands':[
   'scripts/lean_lock.sh lake build MaxCaterpillar.Fiber.NaturalInterventions',
   'scripts/lean_lock.sh lake env lean -j1 verification/fiber/NaturalInterventionsCheck.lean',
   'python3 research/sN/zulip_three/activation_receipt.py'
 ],
 'module_build_exit_code':0,
 'exact_type_check_exit_code':0,
 'axiom_checks':audit,
 'source_sha256':dict(sorted(sources.items())),
 'log_sha256':{name:hashlib.sha256((OUT/name).read_bytes()).hexdigest() for name in
               ['activation_build.log','activation_module.log','activation_exact.log']},
 'receipt_kind':'Source-bound scoped working-tree verification; public-root integration is performed by the parent task.',
 'not_claimed':'This statement does not identify natural activation equivalence with arbitrary causal-abstraction equivalence, and does not assert equality of the pre-ReLU preactivation maps.'
}
(OUT/'activation_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'axiom_checks':len(audit),'source_files':len(sources),'headline':receipt['headline']},indent=2))
