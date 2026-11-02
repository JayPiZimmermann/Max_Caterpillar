"""Reproduce isolated crease-cube research controls and Lean helper audits.

This does not formalize the distributional crease-span counterexample.
The receipt labels that general argument separately from kernel claims.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
REL = HERE.relative_to(ROOT)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def run(tag, args):
    result = subprocess.run(args, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE / f'{tag}.log').write_text(result.stdout)
    (HERE / f'{tag}.exit').write_text(str(result.returncode) + '\n')
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout


run('cube_transport', ['python3', str(REL / 'cube_transport.py')])
run('forest_anchor_counterexample', ['python3', str(REL / 'forest_anchor_counterexample.py')])
audits = []
for name, tag in [('Rectangle', 'rectangle_lean'), ('AnchorControls', 'anchor_controls_lean')]:
    log = run(tag, ['lake', 'env', 'lean', '-j1', str(REL / f'{name}.lean')])
    for declaration, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        axioms = {a.strip() for a in text.split(',') if a.strip()}
        assert axioms <= ALLOWED, (declaration, axioms)
        audits.append({'declaration': declaration, 'axioms': sorted(axioms)})
assert {a['declaration'].rsplit('.', 1)[-1] for a in audits} == {
    'relu_rectangle', 'relu_rectangle_function',
    'anchored_last_increment_zero', 'anchored_mixed_increment_zero'}
assert len(audits) == 4
files = list(HERE.glob('*.py')) + list(HERE.glob('*.lean'))
files += [HERE / 'README.md', HERE / 'cube_transport_result.json',
          HERE / 'forest_anchor_counterexample_result.json',
          HERE / 'rectangle_lean.log', HERE / 'anchor_controls_lean.log',
          ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
pending = list(HERE.glob('*.lean'))
seen = set(files)
while pending:
    source = pending.pop()
    for name in re.findall(r'^import\s+(\S+)', source.read_text(), re.M):
        path = ROOT / (name.replace('.', '/') + '.lean')
        if path.is_file() and path not in seen:
            seen.add(path)
            pending.append(path)
receipt = {
    'status': 'PASS',
    'evidence_kind': 'Content-bound isolated research controls, not a clean public claim gate.',
    'scope': 'Reproduction of finite exact cube/rank/forest controls and exact-type/standard-axiom checks for four elementary Lean helper declarations.',
    'claim_states': {
        'rectangle_identity': 'Lean verified for arbitrary real parameters and arbitrary shared nonlinear preactivation.',
        'anchor_last_and_mixed_increments': 'Lean verified general finite set-function controls.',
        'forest_to_Cr_unitwise_span_refutation': 'General all-real mathematical proof in README.md, with independent integer controls and full-rank spanning-tree witnesses; analytic crease invariant is not Lean formalized.',
        'mixed_cube_tensor_kernel': 'General elementary mathematical proof in README.md; exact finite ranks and rational dimension controls for endpoint grid {-1,0,1}, r=1,2,3.',
        'H_k_three': 'Open. No stronger MAX obstruction or quantitative lower bound is claimed.',
    },
    'axiom_audits': audits,
    'scope_limits': [
        'Unitwise span reduction is refuted, not a cancellation-sensitive reduction of a whole glued network.',
        'The full-rank tree controls show ridge-rank pruning does not restore that unitwise claim.',
        'A single complete cube can hide an off-cube kink and nonzero full Mobius.',
        'Published/frozen Lean modules were not edited or integrated with these research helpers.',
    ],
    'source_and_control_sha256': {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(seen)},
}
(HERE / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'lean_axiom_audits': len(audits),
                  'bound_files': len(seen)}, indent=2))
