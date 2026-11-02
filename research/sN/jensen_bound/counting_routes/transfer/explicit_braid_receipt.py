"""Exact source/type/axiom receipt for the explicit conditional braid consequences."""
from pathlib import Path
import hashlib
import json
import re
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
LOGDIR = HERE.parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidSqrtCorollary'
DRIVERS = [Path('verification/h2/ExplicitBraidCorollaryCheck.lean'),
           Path('verification/h2/ExplicitBraidSqrtCorollaryCheck.lean')]
STEMS = ['braid_parameters_build', 'braid_corollary_final_build', 'braid_corollary_check',
         'braid_sqrt_corollary_build', 'braid_sqrt_corollary_check']
for stem in STEMS:
    assert (LOGDIR / (stem + '.exit')).read_text().strip() == '0', stem
checks = {}
for stem in ['braid_parameters_build', 'braid_corollary_check', 'braid_sqrt_corollary_check']:
    log = (LOGDIR / (stem + '.log')).read_text()
    for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        axioms = sorted(x.strip() for x in text.split(',') if x.strip())
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
        checks[name] = axioms
names = ['braid_parameter_bounds', 'falling_tail_envelope_le', 'exp_shift_le',
         'perNeuronEnvelope_le_four_sq_div_pow', 'braid_envelope_le',
         'conditional_braid_integer_q_lower_bound', 'braidSqrtMatching_bounds',
         'braidSqrtMatching_eq_floor', 'conditional_braid_sqrt_floor_lower_bound']
assert all(any(name.endswith('.' + expected) for name in checks) for expected in names)
paths = set(DRIVERS + [Path('lean-toolchain'), Path('lake-manifest.json')])
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
    'object_scope': 'Actual NormalizedNetwork n h1 h2, TranslationNormalized, exact MAX_n on every real input, with every first-row support of cardinality at most two.',
    'conditional_premise': 'Explicit LocalMatchingObstruction (4*q+1) q, concerning actual local MAX networks; growing levels are not asserted here.',
    'integer_q_theorem': 'q>=1 and 160000*q^2<=n imply h2>=(23/25)*4^q under the explicit local structural hypothesis.',
    'sqrt_floor_theorem': 'n>=160000 and H(4*floor(sqrt(n)/400)+1,floor(sqrt(n)/400)) imply h2>=(23/25)*4^floor(sqrt(n)/400).',
    'derived_choices': 'k=4*q+1, m=n-k, K=floor(m/100), c=7*K/(24*m*(m-1)). Every floor, positivity, matching-size and ambient-dimension side condition is proved.',
    'scalar_method': 'Actual falling-factorial ratio cancellation, exp(1/7)<=7/6 from the geometric-series bound, shift<=q/7, and base<=1/4 from160000*q^2<=n.',
    'actual_network_bridge': 'Instantiates the proved actual conditional_finite_transfer; both first-support bad statistics vanish from the braid row hypothesis. No finite(T), envelope, event, survival, or probability inequality is assumed in either final network consequence.',
    'dimension_instances': 'Required ambient NeZero n is derived internally from the size hypotheses. Natural existing MAX_n arguments were checked by an independent consumer.',
    'raw_affine_scope': 'Raw AffineSkipNetwork wrappers are separate work in GrowingMatching.AffineBraid; this receipt certifies normalized-model consequences.',
    'axiom_checks': checks,
    'project_source_count': sum(p.suffix == '.lean' for p in paths),
    'source_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)},
}
(HERE / 'explicit_braid_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: finite-q and exact sqrt-floor conditional braid network consequences; standard axioms only.')
