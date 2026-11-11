"""Content-bound audit of the actual finite per-neuron event cost 400."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.PerNeuron'
DRIVER = Path('verification/h2/PerNeuronCheck.lean')
for stem in ['per_neuron_build', 'per_neuron_check']:
    assert (HERE / (stem + '.exit')).read_text().strip() == '0', stem
log = (HERE / 'per_neuron_check.log').read_text()
assert not re.search(r'error:|sorryAx|Lean\.ofReduceBool', log)
checks = {}
for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    checks[name] = axioms
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    checks[name] = []
main_names = ['neuron_event_card_le_four_hundred', 'exists_neuron_event_counting_threshold']
assert all(any(key.endswith('.' + name) for key in checks) for name in main_names)
assert len(checks) == 23, len(checks)
paths, stack = set(), [MODULE]
while stack:
    name = stack.pop()
    path = Path(*name.split('.')).with_suffix('.lean')
    if path in paths or not (ROOT / path).is_file():
        continue
    paths.add(path)
    for line in (ROOT / path).read_text().splitlines():
        if line.startswith('import '):
            stack.extend(line.split()[1:])
project_sources = sorted(paths)
spec = importlib.util.spec_from_file_location('max_verify_source_scan', ROOT / 'scripts/verify.py')
scanner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scanner)
for path in project_sources + [DRIVER]:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',
        scanner.uncomment((ROOT / path).read_text())), str(path)
paths.update([DRIVER, Path('lean-toolchain'), Path('lake-manifest.json'), Path('lakefile.lean')])
paths.update((HERE / p).relative_to(ROOT) for p in [
    'per_neuron_build.log', 'per_neuron_build.exit', 'per_neuron_check.log',
    'per_neuron_check.exit', 'per_neuron_receipt.py', 'PER_NEURON_ROUTE.md'])
receipt = {
    'status': 'PASS', 'module': MODULE, 'exact_driver': str(DRIVER),
    'scope': 'Actual original second-neuron preactivation at the actual common gap point; literal uniform three-permutation configuration event; arbitrary real normalized skip-network arrays.',
    'main_theorem': main_names[0],
    'hypotheses': ['net : NormalizedNetwork (m+5) h1 h2', 'net.TranslationNormalized',
        'm>=400', 'K>=4', '(K:Real)<=m/100', 'UniformGapScale net T'],
    'conclusion': 'K^2 * card(neuronEvent net hn K T k) <= 400 * card(Configuration m)',
    'threshold_theorem': main_names[1],
    'threshold_scope': 'For every real normalized network there is B>=2 such that all T>=B and all admissible K and original second indices k satisfy the same actual event count; no genericity, rank, probability, or counting premise.',
    'literal_event': 'Actual counted all-first-row-support Good at effective full order, actual rank Qgood, actual original inner_k(actualGapPoint(baseTail sigma)(tau,rho)T)=0, and ambient braid graph having two disjoint edges on the five selected labels.',
    'model_bridges': ['Good implies actual clean dominant-gap condition using original row support.',
        'Actual matching-data permutation fibers have proved single-coin flip equivalences.',
        'Actual restricted effective rows have independent nonzero disjoint matching-root columns.',
        'Actual scalar survival equals actual row vanishing at the same generic point.',
        'Clean event discarded after the conditional rank bound.',
        'Actual all-graph partial-matching moment and deletion count, including empty graphs.',
        'Actual selected two-disjoint-edge finite-permutation count and zero-density-safe outer cancellation.'],
    'nonvacuity': 'Exact driver constructs normalized network on405 inputs, zero first neurons and one genuine second slot; m400,K4 jointly satisfy all numeric hypotheses and the derived actual threshold count applies.',
    'commands': ['lake build ' + MODULE, 'lake env lean -j1 ' + str(DRIVER)],
    'axiom_checks': checks,
    'project_source_closure_count': len(project_sources),
    'working_tree_content_bound': True,
    'source_commit': None,
    'source_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)},
}
(HERE / 'per_neuron_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: actual per-neuron400, exact event/type/nonvacuity, 23 standard-axiom audits,',
      len(project_sources), 'project source hashes.')
