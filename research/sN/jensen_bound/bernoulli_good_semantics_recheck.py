"""Rebuild and audit the intrinsic original-label Bernoulli good-event semantic bridge."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import datetime

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
MODULES = ['MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Weights','MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Semantics']
DRIVER = 'verification/frontier/BernoulliGoodEventSemanticsCheck.lean'
SOURCES = [m.replace('.', '/') + '.lean' for m in MODULES] + [DRIVER]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def run(command, stem):
    result = subprocess.run(command, cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / (stem + '.log')).write_text(result.stdout)
    (OUT / (stem + '.exit')).write_text(str(result.returncode) + '\n')
    if result.returncode:
        raise RuntimeError(f'{stem} failed: {result.returncode}\n{result.stdout}')
    return result.stdout

spec = importlib.util.spec_from_file_location('project_verify', ROOT / 'scripts/verify.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


def closure(files):
    """Return every project Lean source imported transitively by these files."""
    seen = set()
    pending = list(files)
    while pending:
        rel = pending.pop()
        if rel in seen:
            continue
        path = ROOT / rel
        if not path.is_file():
            raise RuntimeError(f'Missing project import source: {rel}')
        seen.add(rel)
        source = verify.uncomment(path.read_text())
        for imports in re.findall(r'^import[ \t]+([^\n]+)', source, re.M):
            for module in imports.split():
                if module.startswith(('MaxCaterpillar', 'MaxNN')):
                    pending.append(module.replace('.', '/') + '.lean')
    return seen


def closure_hashes():
    return {rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
            for rel in sorted(closure(SOURCES))}


before_source_sha256 = closure_hashes()
for path in SOURCES:
    clean = verify.uncomment((ROOT / path).read_text())
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b|Lean\.ofReduceBool', clean)
    if forbidden:
        raise RuntimeError(f'Forbidden constructs in {path}: {forbidden}')

run(['python3', 'research/sN/zulip_three/lean_small_pool.py', 'lake', 'build', *MODULES], 'bernoulli_good_semantics_module')
stdout = run(['python3', 'research/sN/zulip_three/lean_small_pool.py', 'lake', 'env', 'lean', '-j1', DRIVER],
    'bernoulli_good_semantics_exact')
audits = []
for name, entries in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", stdout, re.S):
    axioms = [x.strip() for x in entries.split(',') if x.strip()]
    if not set(axioms) <= ALLOWED:
        raise RuntimeError(f'Unexpected axioms for {name}: {axioms}')
    audits.append({'declaration': name, 'axioms': axioms})
if len(audits) != 8:
    raise RuntimeError(f'Expected eight axiom checks, found {len(audits)}')
source_sha256 = closure_hashes()
if source_sha256 != before_source_sha256:
    changed = sorted(p for p in set(source_sha256) | set(before_source_sha256)
                     if source_sha256.get(p) != before_source_sha256.get(p))
    raise RuntimeError(f'Project import closure changed during verification: {changed}')

receipt = {
    'status': 'PASS',
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Original arbitrary real zero-sum rows on Fin n with support at least three force literal intrinsic selected-subset bad-event membership from an actual isolated dominant gap. Complement of the finite family bad event over all original first supports implies ActualClean for every original second neuron, using the frozen Sampling tail enumeration and frozen dominant-gap collapsed row. No full-position permutation, label cast, assumed run partition, bad-role witness, probability estimate or ActualClean conclusion is a premise.',
    'not_claimed': 'Bernoulli/Harris aggregation, quantitative bad-event bounds or a network width bound.',
    'modules': MODULES,
    'exact_type_driver': DRIVER,
    'axiom_checks': audits,
    'source_sha256': source_sha256,
    'project_import_closure_sources': len(source_sha256),
    'source_closure_stable_during_verification': True,
    'exact_log_sha256': hashlib.sha256((OUT / 'bernoulli_good_semantics_exact.log').read_bytes()).hexdigest(),
    'recheck_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'toolchain_sha256': hashlib.sha256((ROOT / 'lean-toolchain').read_bytes()).hexdigest(),
    'lake_manifest_sha256': hashlib.sha256((ROOT / 'lake-manifest.json').read_bytes()).hexdigest(),
    'receipt_kind': 'Scoped working-tree module/type/axiom receipt; no clean publication gate is claimed.',
    'reproduce': 'python3 research/sN/jensen_bound/bernoulli_good_semantics_recheck.py',
}
(OUT / 'bernoulli_good_semantics_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'status': receipt['status'], 'axiom_checks': len(audits), 'source_files': len(source_sha256)}, indent=2))
