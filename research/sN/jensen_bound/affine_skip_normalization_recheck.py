#!/usr/bin/env python3
"""Build and independently re-elaborate the nine-array affine-skip bridge."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization'
DRIVER = 'verification/h2/AffineSkipNormalizationCheck.lean'
PREFIX = 'MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension.'
NAMES = ['homogeneousExtension_eval', 'homogeneousModel_exact_direction',
         'homogeneousModel_computes_max', 'homogeneousModel_first_row',
         'homogeneousModel_feeding_original', 'diagonalModel_computes_max',
         'normalizedModel_computes_max', 'normalizedModel_translation_normalized',
         'normalizedModel_first_row', 'normalizedModel_feeding_original',
         'exists_normalizedModel']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def closure():
    result = {}
    def visit(path):
        key = str(path.relative_to(ROOT))
        if key in result:
            return
        result[key] = sha(path)
        for name in re.findall(r'^import\s+([^\s]+)', path.read_text(), re.M):
            child = ROOT / (name.replace('.', '/') + '.lean')
            if child.is_file():
                visit(child)
    visit(ROOT / DRIVER)
    return result

# Reuse the maintained lexical scanner only, not any theorem contract.
sys.path.insert(0, str(ROOT / 'scripts'))
from verify import uncomment

before = closure()
checks = [('affine_skip_normalization_root', ['lake', 'build', MODULE]),
          ('affine_skip_normalization_exact', ['lake', 'env', 'lean', '-j1', DRIVER])]
if '--run' in sys.argv:
    for name, args in checks:
        with (HERE / (name + '.log')).open('w') as stream:
            proc = subprocess.run([str(ROOT / 'scripts/lean_lock.sh'), *args],
                                  cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        (HERE / (name + '.exit')).write_text(str(proc.returncode) + '\n')
        if proc.returncode:
            raise SystemExit(f'FAILED {name}: {proc.returncode}')

logs = {}
for name, _ in checks:
    assert (HERE / (name + '.exit')).read_text().strip() == '0', name
    path = HERE / (name + '.log')
    logs[str(path.relative_to(ROOT))] = sha(path)
text = (HERE / 'affine_skip_normalization_exact.log').read_text()
axioms = {}
for short in NAMES:
    name = PREFIX + short
    match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", text, re.S)
    assert match, name
    deps = sorted(x.strip() for x in match[1].split(',') if x.strip())
    assert set(deps) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, deps)
    axioms[name] = deps
for path in before:
    code = uncomment((ROOT / path).read_text())
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',
                         code, re.M), path
after = closure()
assert before == after, 'Source changed during gate'
receipt = {
    'status': 'PASS', 'module': MODULE, 'driver': DRIVER,
    'source_count': len(after), 'source_files': after, 'logs': logs,
    'headline_axioms': axioms, 'forbidden_construct_scan': 'PASS',
    'scope': 'Nine unrestricted real arrays A,b,W,U,theta,d,B,L,beta, arbitrary affine input/output skips and biases, exact MAX_N on every real input: an explicit normalized model on the SAME original Fin h1 and Fin h2, full zero-sum first/second forms and unit output slope. Only NeZero N is assumed.',
    'first_row_lineage': 'Exact original row A_j iff original b_j=0 and sum_i A_ji=0; otherwise zero. No scaling, merging, neuron creation, or index replacement.',
    'feeding_lineage': 'Every nonzero normalized first-to-second column has an original nonzero W_kj. Output-only first terms are retained in the explicit B output term, not silently counted as feeding.',
    'method': 'An extra INPUT constant coordinate encodes affine arrays; the existing exact directional theorem at that coordinate unit vector proves bias removal. An all-ones directional pass and the existing outer normalization prove the translation-normalized target equation.',
    'independent_contract': 'Handwritten expanded nine-array source evaluator and expanded six-array normalized evaluator, all normalization sums, exact original coefficient mask, and nonzero-coefficient feeding lineage.',
    'nonvacuity': 'A biased affine-skip one-coordinate witness with original nonzero W and input skip, plus a nonlinear actual MAX3 network at unchanged widths (4,3).',
    'reproduce': 'python3 research/sN/jensen_bound/affine_skip_normalization_recheck.py --run',
    'toolchain_sha256': sha(ROOT / 'lean-toolchain')}
path = HERE / 'affine_skip_normalization_receipt.json'
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(f'PASS {len(after)} current project sources, {len(axioms)} standard-only audits: {path.relative_to(ROOT)}')
