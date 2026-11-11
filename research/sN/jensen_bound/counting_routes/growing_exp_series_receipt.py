"""Receipt for scalar exponential-series helpers in the conditional arity route."""
from pathlib import Path
import hashlib
import json
import re
ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
for stem in ['growing_exp_series_final_build', 'growing_exp_series_check']:
    assert (HERE / (stem + '.exit')).read_text().strip() == '0', stem
log = (HERE / 'growing_exp_series_check.log').read_text()
checks = {}
for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    checks[name] = axioms
names = ['pow_mul_exp_neg_div_factorial_le_inv_pow', 'le_shifted_exp_envelope']
assert all(any(name.endswith('.' + expected) for name in checks) for expected in names)
paths = [Path('MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/ExpSeries.lean'),
         Path('verification/h2/GrowingExpSeriesCheck.lean'), Path('lean-toolchain'),
         Path('lake-manifest.json'), Path(__file__).resolve().relative_to(ROOT)]
paths += [(HERE / (stem + ext)).relative_to(ROOT)
          for stem in ['growing_exp_series_final_build', 'growing_exp_series_check']
          for ext in ['.log', '.exit']]
receipt = {
    'status': 'PASS',
    'scope': 'Scalar exponential-series inequalities only; no local structural matching hypothesis or unconditional network lower bound is established here.',
    'core': 'eta^q * exp(-(c*eta)) / q! <= (c^q)^(-1), for c>0, eta>=0, q:Nat.',
    'shifted': 'P<=A*eta^q/q!*exp(-(c*(eta-d))) implies P<=A*(c^q)^(-1)*exp(c*d), for A>=0,c>0,eta>=0, arbitrary real P,d.',
    'method': 'One nonnegative term of the real exponential series, Real.pow_div_factorial_le_exp; then positive multiplication and exact field algebra. No calculus or Stirling estimate.',
    'power_notation': 'The Lean type explicitly uses inverse of c^q; no natural-number negation is used.',
    'boundary_checks': ['q=0', 'eta=0'],
    'axiom_checks': checks,
    'source_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
}
(HERE / 'growing_exp_series_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: exponential-series scalar bound and shifted envelope transfer.')
