"""Bind the literal Bernoulli scalar choices and derived numerical estimates."""
from pathlib import Path
import hashlib
import json
import re
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
LOGDIR = HERE.parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters'
DRIVER = Path('verification/h2/BernoulliParametersCheck.lean')
STEMS = ['bernoulli_exponential_basic_build', 'bernoulli_exponential_final_build',
         'bernoulli_parameters_final_build', 'bernoulli_parameters_check']
for stem in STEMS:
    assert (LOGDIR / (stem + '.exit')).read_text().strip() == '0', stem
log = (LOGDIR / 'bernoulli_parameters_check.log').read_text()
checks = {}
for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    checks[name] = axioms
names = ['parameter_bounds', 'supportBudget_le', 'shortQ_budget_le', 'neuronEnvelope_le_strong',
         'neuronEnvelope_le', 'noInternalExponent_le', 'admissible_denominator_lower',
         'conditioned_size_ratio_le', 'coverage_from_explicit_budgets', 'conditional_width_bound']
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
paths.update((LOGDIR / (stem + ext)).relative_to(ROOT)
             for stem in STEMS for ext in ['.log', '.exit'])
paths.add(Path(__file__).resolve().relative_to(ROOT))
receipt = {
    'status': 'PASS', 'module': MODULE,
    'scope': 'Pure scalar and literal finite parameter estimates for the Bernoulli conditional route; actual probability laws, structural hypotheses and network event-union proofs are separate modules.',
    'hypotheses': 'd:Nat>=1 and n>=10^10*d^2.',
    'literal_choices': 'p=1/(1000*d*sqrt(n)), mu=sqrt(n)/(1000*d), delta=1/(1000*d^2), K=floor(delta*n), q=floor(mu/8), k0=4*q+1, cap=floor(2*mu), m0=n-cap, c0=7*K/(24*n^2).',
    'floor_and_positivity': 'mu>=100, q>=mu/9>=1, k0<=3mu/5, cap<=2mu, n<=2m0, m0>=400, delta*n/2<=K<=delta*n, 4<=K,100K<=m0, and k0<=cap. Exact p*n=mu,p^2*n=alpha^2 and K real-floor bridge are proved.',
    'support_and_shortQ': 'G<=1/1000 for 0<=L<=d^2*n^2 using actual descending factorial denominators;8K/m0<=16/1000.',
    'envelope': '(p^2/c0)^q*exp(c0*cap*(n-1))<=exp(-(7/18-1/1000)*mu)<=exp(-3mu/8). The base48/7000 and shift<=mu/1000 are derived, not assumed.',
    'conditioning': '2Mp^3<=2e-6*mu for M<=d^2*n^2; explicit admissible denominator>=.5exp(-2e-6*mu)>0 and exact conditioned selected-size ratio<=1/100.',
    'coverage': 'The three explicit bad-event upper formulas imply conditional remaining mass>=9/10.',
    'width_scalar': 'Given the finite conditional union inequality9/10<=h2*neuronEnvelope, h2>=(9/10)*exp(3mu/8), hence h2>=(1/2)*exp(3sqrt(n)/(8000d)). This antecedent is explicit and is proved by separate actual-model assembly.',
    'audit_style': 'Symbolic expected types and transitive axioms; no concrete numerical sqrt evaluation.',
    'axiom_checks': checks,
    'project_source_count': sum(p.suffix == '.lean' for p in paths),
    'source_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)},
}
(HERE / 'bernoulli_parameters_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: literal Bernoulli sqrt parameters, error/envelope budgets, and scalar conditional width transfer.')
