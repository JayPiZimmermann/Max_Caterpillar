"""Check the public-root claims; run under scripts/lean_lock.sh."""
from datetime import datetime, timezone
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'public_claim_manifest.json'
manifest = json.loads(MANIFEST.read_text())
spec = importlib.util.spec_from_file_location('source_verifier', ROOT / 'scripts/verify.py')
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)

pending = [ROOT / 'MaxCaterpillar.lean', ROOT / 'All.lean', ROOT / manifest['exact_expected_types'],
           ROOT / 'verification/fiber/PublicCheck.lean']
sources = set()
while pending:
    path = pending.pop()
    if path in sources:
        continue
    sources.add(path)
    code = verifier.uncomment(path.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code), path
    for imports in re.findall(r'^import\s+([^\n]+)', code, re.M):
        for imported in imports.split():
            dependency = ROOT / (imported.replace('.', '/') + '.lean')
            if dependency.is_file():
                pending.append(dependency)
for claim in manifest['claims']:
    assert ROOT / (claim['module'].replace('.', '/') + '.lean') in sources, claim
sources.update([MANIFEST, Path(__file__).resolve(), ROOT / 'scripts/verify.py',
                ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain'])

def hashes():
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
            for path in sorted(sources)}

before = hashes()
commands = [
    ('root', ['lake', 'build', manifest['root']]),
    ('all', ['lake', 'build', 'All']),
    ('exact', ['lake', 'env', 'lean', '-j1', manifest['exact_expected_types']]),
    ('compatibility', ['lake', 'env', 'lean', '-j1', 'verification/fiber/PublicCheck.lean']),
]
results = []
logs = {}
for name, command in commands:
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logs[name] = result.stdout
    (HERE / f'public_{name}.log').write_text(result.stdout)
    (HERE / f'public_{name}.exit').write_text(str(result.returncode) + '\n')
    results.append({'command': command, 'exit_code': result.returncode})
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
checks = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", logs['exact']):
    checks[name] = sorted(a.strip() for a in axioms.split(',') if a.strip())
expected = {claim['declaration'] for claim in manifest['claims']}
assert checks.keys() == expected, (checks.keys(), expected)
assert all(set(axioms) <= set(manifest['allowed_axioms']) for axioms in checks.values())
assert before == hashes(), 'Sources changed during verification; rerun the gate.'
receipt = {
    'status': 'PASS', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'scope': manifest['scope'],
    'evidence_kind': 'Rebuilt public-root working-tree exact-type and axiom gate; not a clean-commit publication receipt.',
    'commands': results, 'axiom_checks': checks, 'source_sha256': before,
    'source_unchanged': True,
    'log_sha256': {name: sha256(log.encode()).hexdigest() for name, log in logs.items()},
}
(HERE / 'public_claim_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'headline_claims': len(checks),
                  'source_files': len(sources)}, indent=2))
