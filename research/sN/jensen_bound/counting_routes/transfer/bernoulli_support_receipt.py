"""Content-bound symbolic receipt for the Bernoulli support budget scalar step."""
from pathlib import Path
import hashlib
import json
import re
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.SupportBudget'
DRIVER = Path('verification/h2/BernoulliSupportBudgetCheck.lean')
STEMS = ['bernoulli_support_final_build', 'bernoulli_support_check']
for stem in STEMS:
    assert (HERE / (stem + '.exit')).read_text().strip() == '0', stem
log = (HERE / 'bernoulli_support_check.log').read_text()
checks = {}
for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    checks[name] = axioms
names = ['generic_supportBudget_le', 'support_constants_le', 'supportBudget_le', 'shortQ_budget_le']
assert all(any(name.endswith('.' + expected) for name in checks) for expected in names)
paths = {DRIVER, Path('lean-toolchain'), Path('lake-manifest.json')}
stack = [MODULE]
while stack:
    name = stack.pop()
    path = Path(*name.split('.')).with_suffix('.lean')
    if path in paths or not (ROOT / path).is_file():
        continue
    paths.add(path)
    for line in (ROOT / path).read_text().splitlines():
        if line.startswith('import '):
            stack.extend(line.split()[1:])
paths.update((HERE / (stem + ext)).relative_to(ROOT)
             for stem in STEMS for ext in ['.log', '.exit'])
paths.add(Path(__file__).resolve().relative_to(ROOT))
receipt = {
    'status': 'PASS', 'module': MODULE,
    'scope': 'Scalar-only support-contamination and short-Q ratios for literal Bernoulli parameters; no structural, probability, or network conclusion is assumed or asserted.',
    'literal_hypotheses': 'd:Nat>=1, n:Nat>=10^10*d^2, 0<=L<=(d:Real)^2*(n:Real)^2.',
    'support_bound': 'supportBudget n d L <=1/1000, with the exact three-term G defined in Defs.',
    'short_Q_bound': '8*rankCount n d/minimumTail n d <=16/1000.',
    'factorial_estimates': 'Genuine descending factorials satisfy (m)_4>=m^4/4, (m)_3>=m^3/2, (m)_2>=m^2/2 at the proved minimum tail size.',
    'term_bounds': ['128*D*delta^2', '64*D*p*delta^2', '4*D*alpha^2*delta'],
    'numeric_margin': '128/10^6 +64/10^6 +4/10^9 <=1/1000.',
    'proof_method': 'Symbolic floor/sqrt side conditions and exact p^2*n=alpha^2 from Floors; direct order/division algebra, actual factorial lower estimates, literal alpha/delta identities. No concrete numerical square-root evaluation.',
    'axiom_checks': checks,
    'source_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)},
}
(HERE / 'bernoulli_support_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: literal symbolic Bernoulli support budget and short-Q scalar ratios.')
