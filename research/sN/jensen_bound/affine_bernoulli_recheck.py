#!/usr/bin/env python3
"""Exact original affine-skip conditional Bernoulli sqrt gate."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.AffineLowerBound'
DRIVERS = ['verification/h2/AffineBernoulliHalfCheck.lean',
           'verification/h2/AffineBernoulliLowerBoundCheck.lean']
PREFIX = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Affine.'
HEADLINES = [PREFIX + name for name in ['exists_affine_quadratic_half_budgets',
    'matchingOrder_eq_sqrt_floor', 'conditional_affine_sqrt_lower_bound',
    'conditional_affine_sqrt_lower_bound_explicit']]

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
    for driver in DRIVERS:
        visit(ROOT / driver)
    return result

sys.path.insert(0, str(ROOT / 'scripts'))
from verify import uncomment

before = closure()
checks = [('affine_bernoulli_root', ['lake', 'build', MODULE]),
          ('affine_bernoulli_half_exact', ['lake', 'env', 'lean', '-j1', DRIVERS[0]]),
          ('affine_bernoulli_bound_exact', ['lake', 'env', 'lean', '-j1', DRIVERS[1]])]
if '--run' in sys.argv:
    runner = ([sys.executable, str(ROOT / 'research/sN/zulip_three/lean_small_pool.py')]
              if '--pool' in sys.argv else [str(ROOT / 'scripts/lean_lock.sh')])
    for name, args in checks:
        with (HERE / (name + '.log')).open('w') as stream:
            proc = subprocess.run([*runner, *args], cwd=ROOT,
                                  stdout=stream, stderr=subprocess.STDOUT)
        (HERE / (name + '.exit')).write_text(str(proc.returncode) + '\n')
        if proc.returncode:
            raise SystemExit(f'FAILED {name}: {proc.returncode}')
logs = {}
for name, _ in checks:
    assert (HERE / (name + '.exit')).read_text().strip() == '0', name
    path = HERE / (name + '.log')
    logs[str(path.relative_to(ROOT))] = sha(path)
output = (HERE / 'affine_bernoulli_bound_exact.log').read_text()
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
    'status': 'PASS', 'module': MODULE, 'drivers': DRIVERS,
    'source_count': len(after), 'source_files': after, 'logs': logs,
    'headline_axioms': axioms, 'forbidden_construct_scan': 'PASS',
    'scope': 'Original nine-array AffineSkipNetwork N h1 h2 with arbitrary real first covectors, weights, biases and affine skips, exact MAX_N on ALL real inputs, total original h1<=C*N^2 and integer C>=1. Putn=floor(N/2),d=20*C andq=floor(sqrt(n)/(160000*C)). Ifn>=10^10*d^2 and explicit LocalMatchingObstruction(4q+1,q),then originalh2>=(1/2)*exp(3*sqrt(n)/(160000*C)).',
    'conditional_boundary': 'The growing-order structural obstruction H is an explicit premise and is NOT proved here. This is a conditional square-root exponential arbitrary-first-layer theorem, not an unconditional exponential lower bound.',
    'derived_reductions': 'A concrete raw affine normalization, one actual half coordinate set and generic tied localization, full translation normalization, actual support-count/falling-four budgets, and all dimension positivity instances are derived. Both original finite hidden-layer indices and h2 are preserved.',
    'width_accounting': 'The width budget counts ALL original first neurons, including output-only B terms. No feeding-only substitution, braid, bounded support, bounded overlap, rational-weight or zero-bias restriction is imposed.',
    'no_hidden_analytic_premise': 'Neither the normalized sqrt theorem nor the raw wrapper assumes survival, rank, a probability estimate, a rare-event conditional law, an envelope, or a generic point. Those are proved dependencies; the raw wrapper additionally discharges all model/statistic premises.',
    'floor_identity': 'The actual matchingOrder=floor((sqrt(n)/(1000*d))/8) is proved equal tofloor(sqrt(n)/(8000*d));d20C then gives the exact160000*C denominator in both q and the exponent.',
    'independent_contract': 'Handwritten expected type expands all nine raw arrays, the raw evaluator, original total first-width budget, integer floorN/2, exact q andH arity, every numeric constant, and the final exponential inequality. A separate half contract expands both ALL-first statistics and all normalization sums.',
    'nonvacuity': 'The underlying same-width actual half restriction is checked on nonlinear odd-arity MAX3-to-MAX1 at widths(4,3), independently of the large-size/H premise. No concrete growing-order H witness is claimed. No direct large-number sqrt evaluation is used.',
    'reproduce': 'python3 research/sN/jensen_bound/affine_bernoulli_recheck.py --run',
    'toolchain_sha256': sha(ROOT / 'lean-toolchain')}
path = HERE / 'affine_bernoulli_receipt.json'
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(f'PASS {len(after)} current project sources, {len(axioms)} standard-only audits: {path.relative_to(ROOT)}')
