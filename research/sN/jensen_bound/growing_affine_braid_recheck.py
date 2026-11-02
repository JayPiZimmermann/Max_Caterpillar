#!/usr/bin/env python3
"""Exact raw affine-braid conditional transfer gate; --run reproduces it."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineBraid'
DRIVER = 'verification/h2/GrowingMatchingAffineBraidCheck.lean'
PREFIX = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineBraid.'
HEADLINES = [PREFIX + name for name in ['normalizedModel_support_le_two',
             'conditional_affine_braid_integer_q_lower_bound']]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def closure():
    result = {}
    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in result:
            return
        result[rel] = sha(path)
        for name in re.findall(r'^import\s+([^\s]+)', path.read_text(), re.M):
            child = ROOT / (name.replace('.', '/') + '.lean')
            if child.is_file():
                visit(child)
    visit(ROOT / DRIVER)
    return result

sys.path.insert(0, str(ROOT / 'scripts'))
from verify import uncomment

before = closure()
checks = [('growing_affine_braid_root', ['lake', 'build', MODULE]),
          ('growing_affine_braid_exact', ['lake', 'env', 'lean', '-j1', DRIVER])]
if '--run' in sys.argv:
    runner = ([sys.executable, str(ROOT / 'research/sN/zulip_three/lean_small_pool.py')]
              if '--pool' in sys.argv else [str(ROOT / 'scripts/lean_lock.sh')])
    for name, args in checks:
        with (HERE / (name + '.log')).open('w') as stream:
            proc = subprocess.run([*runner, *args],
                                  cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        (HERE / (name + '.exit')).write_text(str(proc.returncode) + '\n')
        if proc.returncode:
            raise SystemExit(f'FAILED {name}: {proc.returncode}')
logs = {}
for name, _ in checks:
    assert (HERE / (name + '.exit')).read_text().strip() == '0', name
    path = HERE / (name + '.log')
    logs[str(path.relative_to(ROOT))] = sha(path)
output = (HERE / 'growing_affine_braid_exact.log').read_text()
axioms = {}
for name in HEADLINES:
    match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", output, re.S)
    assert match, name
    deps = sorted(x.strip() for x in match[1].split(',') if x.strip())
    assert set(deps) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, deps)
    axioms[name] = deps
for rel in before:
    code = uncomment((ROOT / rel).read_text())
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',
                         code, re.M), rel
after = closure()
assert before == after, 'Source changed during gate'
receipt = {
    'status': 'PASS', 'module': MODULE, 'driver': DRIVER,
    'source_count': len(after), 'source_files': after, 'logs': logs,
    'headline_axioms': axioms, 'forbidden_construct_scan': 'PASS',
    'scope': 'Raw AffineSkipNetwork N h1 h2 with nine unrestricted real parameter arrays, arbitrary biases and affine skips, exact MAX_N on every real input, and the ORIGINAL braid condition sum(A_j)=0 implies support(A_j).card<=2. For q>=1 and160000*q^2<=N, LocalMatchingObstruction(4*q+1,q) implies (23/25)*4^q<=h2.',
    'normalization': 'Derived from the frozen faithful AffineSkipNormalization bridge, preserving original Fin h1/Fin h2. Every surviving first covector is exactly its original zero-bias zero-sum vector; therefore normalized braid support is proved from the original braid condition.',
    'conditional_boundary': 'LocalMatchingObstruction(4*q+1,q) is an explicit premise. This receipt does NOT prove that obstruction at growing q and does NOT establish an unconditional exponential lower bound.',
    'independent_contract': 'Expanded raw nine-array evaluator, original zero-sum covector support predicate and literal arity4*q+1. No normalized-model, random-scale, envelope, rank, probability or width-budget premise is supplied.',
    'nonvacuity': 'The raw exact-MAX and braid premises hold jointly for the nonlinear MAX3 network. A dense biased nonzero-sum row is separately admitted by the raw braid predicate and demonstrably deleted by normalization. No witness for growing H is claimed.',
    'reproduce': 'python3 research/sN/jensen_bound/growing_affine_braid_recheck.py --run',
    'toolchain_sha256': sha(ROOT / 'lean-toolchain')}
path = HERE / 'growing_affine_braid_receipt.json'
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(f'PASS {len(after)} current project sources, {len(axioms)} standard-only audits: {path.relative_to(ROOT)}')
