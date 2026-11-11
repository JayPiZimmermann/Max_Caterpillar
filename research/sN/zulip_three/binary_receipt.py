"""Record source-bound completed binary-pattern Lean checks; does not replace compilation."""
from pathlib import Path
from datetime import datetime, timezone
import re, json, hashlib, importlib.util
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/sN/zulip_three'
MODULE='MaxCaterpillar.Fiber.BinaryPatterns'
CHECK=Path('verification/fiber/BinaryPatternsCheck.lean')
for name in ['binary_core_build','binary_update_build2','binary_module','binary_exact']:
    assert (OUT/(name+'.exit')).read_text().strip()=='0',name
log=(OUT/'binary_exact.log').read_text()
assert ': error:' not in log
entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
assert len(entries)==12,len(entries)
allowed={'propext','Classical.choice','Quot.sound'}
audit=[]
for decl,raw in entries:
    axioms={a.strip() for a in raw.split(',') if a.strip()}
    assert axioms<=allowed,(decl,axioms)
    audit.append({'declaration':decl,'axioms':sorted(axioms)})
spec=importlib.util.spec_from_file_location('project_verify',ROOT/'scripts/verify.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
sources={}
def visit(module):
    p=Path(*module.split('.')).with_suffix('.lean')
    if str(p) in sources or not (ROOT/p).is_file():return
    content=(ROOT/p).read_bytes()
    sources[str(p)]=hashlib.sha256(content).hexdigest()
    clean=verify.uncomment(content.decode())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),str(p)
    for line in clean.splitlines():
        if line.startswith('import '):
            for imported in line[7:].split():visit(imported)
visit(MODULE)
for p in [CHECK,Path('lean-toolchain'),Path('lake-manifest.json'),Path('scripts/verify.py'),
          Path('research/sN/zulip_three/binary_receipt.py')]:
    sources[str(p)]=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',verify.uncomment((ROOT/CHECK).read_text()))
receipt={
 'status':'PASS','checked_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'Actual globally exact Max4 (6,3) networks in one full exact-fiber path component; binary active predicates change in BOTH layers, with strict negative-to-positive tracked preactivations. The whole explicit path is bias-free and all three output weights stay nonzero. Both endpoint hidden-layer active counts on the diagonal change from one to two. Existing arbitrary-bias width lower bounds establish minimum widths.',
 'headline':'MaxCaterpillar.Fiber.BinaryPatterns.strict_connected_binary_pattern_counterexample',
 'binary_bits':'MaxCaterpillar.Fiber.BinaryPatterns.strict_binary_gate_changes',
 'path':'MaxCaterpillar.Fiber.BinaryPatterns.strictPath',
 'path_biasfree':'MaxCaterpillar.Fiber.BinaryPatterns.strictPath_zeroBiases',
 'path_output_nonzero':'MaxCaterpillar.Fiber.BinaryPatterns.strictPath_output_nonzero',
 'minimum_widths':'MaxCaterpillar.Fiber.BinaryPatterns.widths_minimal',
 'strict_input':[0,0,1,1],'first_changed_neuron_zero_based':2,'second_changed_neuron_zero_based':1,
 'first_preactivation_endpoints':[-1,1],'second_preactivation_endpoints':[-1,2],
 'active_count_input':[1,1,1,1],'first_active_count_endpoints':[1,2],'second_active_count_endpoints':[1,2],
 'binary_convention':'Active iff physical preactivation >0, equivalently post-ReLU hidden activation >0. Strict witness endpoints do not depend on how zero preactivations are classified.',
 'semantic_checks':[
  'Network.firstBinary and secondBinary are bridged to the direct physical affine preactivations.',
  'The half-line t>=0 family is proved exact on ALL real inputs, not only benchmark samples.',
  'The extra inactive-side leg preserves BOTH full post-ReLU hidden maps on every real input.',
  'The strict path is the actual Mathlib Path.trans composition in the physical Network subspace topology.',
  'The two active-count changes give more than a neuron relabelling at the diagonal input.',
  'No fiber singularity claim is made for the binary-pattern path; ambient regularity of the separate constant-gating family is audited independently.'
 ],
 'commands':[
  'flock /tmp/max_caterpillar_zulip_three_lean.lock lake build MaxCaterpillar.Fiber.BinaryPatterns',
  'flock /tmp/max_caterpillar_zulip_three_lean.lock lake env lean -j1 verification/fiber/BinaryPatternsCheck.lean',
  'python3 research/sN/zulip_three/binary_receipt.py'
 ],
 'module_build_exit_code':0,'exact_type_check_exit_code':0,'axiom_checks':audit,
 'source_sha256':dict(sorted(sources.items())),
 'log_sha256':{n:hashlib.sha256((OUT/n).read_bytes()).hexdigest() for n in ['binary_core_build.log','binary_update_build2.log','binary_module.log','binary_exact.log']},
 'forbidden_construct_scan':'PASS for complete project-source import closure and exact-type driver',
 'receipt_kind':'Source-bound scoped working-tree verification; parent owns public integration gate.'
}
(OUT/'binary_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','source_files':len(sources),'axiom_checks':len(audit)},indent=2))
