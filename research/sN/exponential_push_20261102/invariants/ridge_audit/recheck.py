"""Independent ridge headline audit. Run under the shared Lean lock.

The sibling producer is read-only and must already have matching artifacts.
No original source producer is rebuilt or changed by this audit.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
REL = HERE.relative_to(ROOT)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def run(tag, args):
    r = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    (HERE / f'{tag}.log').write_text(r.stdout)
    (HERE / f'{tag}.exit').write_text(str(r.returncode) + '\n')
    if r.returncode:
        print(r.stdout)
        raise SystemExit(r.returncode)
    return r.stdout


run('tent_control', ['python3', str(REL / 'tent_control.py')])
log = run('exact', ['lake', 'env', 'lean', '-j1', str(REL / 'ExactCheck.lean')])
checks = []
for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = {a.strip() for a in text.split(',') if a.strip()}
    assert axioms <= ALLOWED, (name, axioms)
    checks.append({'declaration': name, 'axioms': sorted(axioms)})
assert len(checks) == 3
assert {x['declaration'] for x in checks} == {
    'IndependentRidgeAudit.actual_input_witness',
    'IndependentRidgeAudit.diagonal_period_countercontrol',
    'IndependentRidgeAudit.one_input_countercontrol'}
seen = {HERE / 'ExactCheck.lean', HERE / 'README.md', HERE / 'recheck.py',
        HERE / 'tent_control.py', HERE / 'tent_control_result.json', HERE / 'exact.log',
        ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json'}
pending = [HERE / 'ExactCheck.lean']
while pending:
    source = pending.pop()
    for name in re.findall(r'^import\s+(\S+)', source.read_text(), re.M):
        path = ROOT / (name.replace('.', '/') + '.lean')
        if path.is_file() and path not in seen:
            seen.add(path)
            pending.append(path)
receipt = {
    'status': 'PASS',
    'scope': 'Independent exact-type and boundary audit of the arbitrary-periodic-summand MAX theorem, plus 2728 independent exact rational tent-identity controls.',
    'verdict': 'No mathematical or semantic gap found in the stable core theorem. Actual network/kernel/rank adapters are separate claims.',
    'axiom_checks': checks,
    'independence': 'Read-only review of all five producer source files; separate expanded witness driver; N1 and diagonal-period countercontrols; direct rational subset enumeration rather than minimum-coordinate pairing.',
    'limitations': ['Does not justify deleting low-rank terms individually.',
                    'Does not prove any growing-matching obstruction or improved width asymptotic.',
                    'Content-bound workspace audit; source producer artifacts must match the hashed source closure.'],
    'source_and_control_sha256': {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(seen)},
}
(HERE / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'axiom_checks': len(checks), 'bound_files': len(seen)}, indent=2))
