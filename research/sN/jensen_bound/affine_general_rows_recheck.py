#!/usr/bin/env python3
"""Exact raw general-row quadratic-width wrapper gate; --run reproduces it."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows'
DRIVER = 'verification/h2/AffineGeneralRowsCheck.lean'
PREFIX = MODULE + '.'
HEADLINES = [PREFIX + name for name in ['exists_normalized_half_model',
    'exists_affine_half_model', 'fourthMoment_le_quadratic_budget',
    'general_rows_budgets_of_fourthMoment', 'conditional_affine_quadratic_width_lower_bound']]

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
checks = [('affine_general_rows_root', ['lake', 'build', MODULE]),
          ('affine_general_rows_exact', ['lake', 'env', 'lean', '-j1', DRIVER])]
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
output = (HERE / 'affine_general_rows_exact.log').read_text()
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
    'scope': 'Raw nine-array AffineSkipNetwork N h1 h2, arbitrary real weights/biases/affine skips and arbitrary first covectors, exact MAX_N on ALL real inputs. For integer C>=1,total h1<=C*N^2,n=floor(N/2),d=20*C,q>=1,8000*d^2<=n,1000*d^2*q^3<=n and explicit H(4q+1,q), the original h2 is at least (1/2)*(n/(400000*d*q^2))^q.',
    'conditional_boundary': 'H=LocalMatchingObstruction is explicitly assumed. It is not proved at growing q. No unconditional superpolynomial or exponential arbitrary-first-layer theorem is claimed.',
    'actual_reductions': 'Original affine-skip normalization is proved, not supplied; a selected half and generic tied point are constructed with the same original Fin h1/Fin h2. Simultaneous4*fourthMoment<=81*h1 and4*nonBraidCount<=h1 hold for ALL indexed first rows, including output-only B terms.',
    'scalar_budget': 'For both parities,N<=3*n when n>0. The exact half budget gives4*A<=729*C*n^2. Since729*C<=4*(20*C)^2 for C>=1,A<=d^2*n^2. Both the support>=3 count and falling-four support sum are bounded by A.',
    'dimension_instances': 'NeZero N,NeZero floor(N/2),NeZero(4q+1) are derived internally from the stated integer bounds; none is an extra caller hypothesis in the raw headline.',
    'independent_contract': 'All nine original arrays, expanded original evaluator,total natural-number first-width budget,literal d=20*C and H arity4*q+1,integer floor N/2,and exact final inequality. The half-model contract expands full normalization and both ALL-first statistics.',
    'nonvacuity': 'Existing nonlinear ordinary MAX3,embedded in the raw affine-skip model,has an actual MAX1 half model at unchanged widths(4,3). A separate oddN7 scalar-budget contract retains symbolic model statistics. No witness for growingH is claimed.',
    'reproduce': 'python3 research/sN/jensen_bound/affine_general_rows_recheck.py --run',
    'toolchain_sha256': sha(ROOT / 'lean-toolchain')}
path = HERE / 'affine_general_rows_receipt.json'
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(f'PASS {len(after)} current project sources, {len(axioms)} standard-only audits: {path.relative_to(ROOT)}')
