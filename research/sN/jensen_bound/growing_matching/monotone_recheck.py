"""Recheck upward input-arity monotonicity against actual network semantics.

Run under the shared Lean lock. This is a content-bound workspace receipt;
promotion to a public claim still needs the final committed-source gate.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Monotone'
DRIVER = Path('verification/frontier/CountGrowingMatchingMonotoneCheck.lean')
PREFIX = 'monotone'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def run(tag, args):
    result = subprocess.run(args, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE / f'{PREFIX}_{tag}.log').write_text(result.stdout)
    (HERE / f'{PREFIX}_{tag}.exit').write_text(str(result.returncode) + '\n')
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout


run('module', ['lake', 'build', MODULE,
              'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance'])
log = run('exact', ['lake', 'env', 'lean', '-j1', str(DRIVER)])
checks = []
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    got = {x.strip() for x in axioms.split(',') if x.strip()}
    assert got <= ALLOWED, (name, got)
    checks.append({'declaration': name, 'axioms': sorted(got)})
required = {
    'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.'
    'localMatchingObstruction_mono_arity',
    *('GrowingMatchingMonotoneChecks.' + x for x in
      ['expanded_actual_type', 'equal_arity', 'known_five_two_upward', 'six_two']),
}
assert len(checks) == len(required) and required == {x['declaration'] for x in checks}, checks

pending = [ROOT / DRIVER, ROOT / (MODULE.replace('.', '/') + '.lean')]
seen = set()
while pending:
    path = pending.pop()
    if path in seen:
        continue
    seen.add(path)
    for imp in re.findall(r'^import\s+(\S+)', path.read_text(), re.M):
        q = ROOT / (imp.replace('.', '/') + '.lean')
        if q.is_file():
            pending.append(q)
spec = importlib.util.spec_from_file_location('project_source_verifier', ROOT / 'scripts/verify.py')
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
for source in seen:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',
                         verifier.uncomment(source.read_text())), source
seen |= {ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json'}
receipt = {
    'status': 'PASS',
    'scope': 'Upward input-arity monotonicity: actual LocalMatchingObstruction(k0,q) implies actual LocalMatchingObstruction(n,q) for positive arities, k0<=n, and q>0.',
    'evidence_kind': 'Content-bound workspace receipt; final clean-commit publication gate is separate.',
    'build_module': MODULE,
    'exact_driver': str(DRIVER),
    'axiom_checks': checks,
    'proof_method': 'Keep the first k0 coordinates of an arbitrary exact normalized n-input braid/skip MAX network. Enumerate the actual complement as tail. The existing actual structural threshold produces a generic dominant-gap localization at one actual threshold point; all first-row supports already have cardinality at most two, so support exclusion is automatic. Its original outer index has a literal q-matching in the original ambient signed graph. Forget only the endpoint containment in the kept coordinates.',
    'semantic_checks': [
        'Expanded expected type quantifies over actual indexed n-input NormalizedNetwork models, translation normalization, all first supports <=2, and equality to MAX_n on every real input.',
        'Conclusion contains ordinary unordered matchings in the original larger model graph and preserves exactly the same q.',
        'Equal-arity boundary and strict 5-to-6 arity increase both kernel checked.',
        'Unconditional known H(5,2) propagates to all n>=5 while q remains two.',
    ],
    'not_claimed': 'No growth of q with n, graph contraction argument, or unconditional improved quantitative asymptotic lower bound.',
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(seen)},
    'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'exact_log_sha256': hashlib.sha256(log.encode()).hexdigest(),
}
(HERE / f'{PREFIX}_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'axiom_checks': len(checks),
                  'source_closure': len(seen)}, indent=2))
