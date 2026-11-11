"""Source-bound audit of the global binary-map and nonzero-output-sign path theorem."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/sN/zulip_three'
MODULE='MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexitySigns'
CHECK=Path('verification/fiber/GlobalBinaryConvexityCheck.lean')
for name in ['global_convexity_signs_module','global_convexity_exact']:
    assert (OUT/(name+'.exit')).read_text().strip()=='0',name
log=(OUT/'global_convexity_exact.log').read_text()
assert ': error:' not in log
entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log,re.S)
assert len(entries)==14,len(entries)
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
          Path('research/sN/zulip_three/global_convexity_receipt.py')]:
    sources[str(p)]=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',verify.uncomment((ROOT/CHECK).read_text()))
receipt={
 'status':'PASS','checked_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'For ordinary globally exact Max_N ReLU networks of arbitrary widths and biases, equality of BOTH complete labelled binary hidden maps on ALL real inputs, together with matching labelled NONZERO output signs, implies an explicit exact-fiber path. The path preserves both binary maps and every nonzero output sign at every point. Physical first-layer weights and biases need not agree.',
 'hypotheses':[
  'Both endpoints are ordinary six-array Network objects in the all-input ExactFiber N h1 h2, N nonzero.',
  'For every real input the complete labelled physical firstBinary maps agree.',
  'For every real input the complete labelled physical secondBinary maps agree.',
  'Every physical output coefficient is nonzero at both endpoints, and its labelled strict-positive sign agrees.'
 ],
 'not_claimed':'Finite-sample binary-map equality is not the all-real-input hypothesis. Unlabelled gates without aligning neuron permutations, zero output coefficients, and differing output-sign vectors are not covered by this theorem. The theorem gives sufficiency; binary maps can change along other exact paths, as the separate strict counterexample shows.',
 'path':'MaxCaterpillar.Fiber.BinaryPatterns.globalSameBinaryPath',
 'joined':'MaxCaterpillar.Fiber.BinaryPatterns.joined_of_global_binary_maps_output_signs',
 'component_equality':'MaxCaterpillar.Fiber.BinaryPatterns.components_eq_of_global_binary_maps_output_signs',
 'both_binary_maps_preserved':'MaxCaterpillar.Fiber.BinaryPatterns.globalSameBinaryPath_binary',
 'nonzero_output_signs_preserved':'MaxCaterpillar.Fiber.BinaryPatterns.globalSameBinaryPath_output',
 'affine_classification':'MaxCaterpillar.Fiber.BinaryPatterns.AffineHalfspace.binary_gate_alternatives',
 'proof_description':'Equality of nonempty strict-positive affine halfspaces forces a positive common scale, proved algebraically on a transverse line; an everywhere-inactive affine row instead has zero incoming weights and nonpositive bias. Positive first-neuron scaling aligns every noninactive affine row and the full first matrix. Interpolating the remaining inactive biases preserves both full hidden maps. Positive second-neuron scaling normalizes each nonzero readout magnitude; the fixed-first convexity theorem supplies a gate-preserving exact segment; inverse normalization finishes the path. Every stage is a physical parameter path with the canonical product/subspace topology.',
 'nonvacuity':'The exact-type driver checks an actual Max4 pair with equal global binary maps and unchanged nonzero readout signs but first matrix entry (0,0) equal to 1 versus 2. It applies the global theorem without a fixed-first hypothesis.',
 'commands':[
  'flock /tmp/max_caterpillar_zulip_three_lean.lock lake build MaxCaterpillar.Fiber.BinaryPatterns.GlobalConvexitySigns',
  'flock /tmp/max_caterpillar_zulip_three_lean.lock lake env lean -j1 verification/fiber/GlobalBinaryConvexityCheck.lean',
  'python3 research/sN/zulip_three/global_convexity_receipt.py'
 ],
 'module_build_exit_code':0,'exact_type_check_exit_code':0,'axiom_checks':audit,
 'source_sha256':dict(sorted(sources.items())),
 'log_sha256':{n:hashlib.sha256((OUT/n).read_bytes()).hexdigest() for n in ['global_convexity_signs_module.log','global_convexity_exact.log']},
 'forbidden_construct_scan':'PASS for complete project-source import closure and exact-type driver',
 'receipt_kind':'Source-bound scoped working-tree verification; parent owns public integration gate.'
}
(OUT/'global_convexity_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','source_files':len(sources),'axiom_checks':len(audit)},indent=2))
