"""Receipt for actual arbitrary-arity first-exceptional-event counts and lift."""
from pathlib import Path
import hashlib
import json
import re
ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
MODULE = 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirstConfigurations'
DRIVER = Path('verification/h2/GrowingBadFirstCheck.lean')
STEMS = ['growing_bad_first_build', 'growing_bad_first_configurations_final_build',
         'growing_bad_first_check']
for stem in STEMS:
    assert (HERE / (stem + '.exit')).read_text().strip() == '0', stem
log = (HERE / 'growing_bad_first_check.log').read_text()
checks = {}
for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = sorted(x.strip() for x in text.split(',') if x.strip())
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    checks[name] = axioms
names = ['support_containment_card_mul_le', 'badFirstEvent_card_mul_le',
         'badFirstEvent_fraction_le', 'badFirstEvent_empty_of_arity_lt_three',
         'badFirstEvent_card_four_mul_le', 'mem_configurationBadFirstEvent',
         'configurationBadFirstEvent_fraction_le']
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
    'scope': 'Actual arbitrary selected arity k, all-permutation input event, finite row-support family, and exact three-configuration lift. No structural matching H or network lower bound is claimed here.',
    'event': 'B1(k,T) = {sigma | exists j, 3 <= card(Tj) and Tj subset smallRankGaps sigma k}; sigma maps labels to positions.',
    'M': 'Exact number of original indices with support cardinality at least three; no maximum support size or nonempty family assumption.',
    'integer_bound': '|B1|*(n)_3 <= M*(k)_3*card(Perm Fin n), for k<=n.',
    'fraction_bound': '|B1|/card(Perm Fin n) <= M*(k)_3/(n)_3, for k<=n and 3<=n.',
    'quarter_bound': '4*M*(k)_3 <= (n)_3 implies 4*|B1| <= card(Perm Fin n).',
    'proof_method': 'One actual three-element subset per support, exact actual permutation containment law, finite union count; no all-triples overcount or assumed probability bound.',
    'configuration_lift': 'Literal product with all ranks, then actual effective-configuration pullback. Pointwise selected-set preservation proves event membership depends only on original sigma; exact fraction is preserved.',
    'boundaries': ['k<3 gives the empty bad event.', 'The indexed support family may be empty.'],
    'axiom_checks': checks,
    'source_sha256': {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)},
}
(HERE / 'growing_bad_first_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: actual arbitrary-arity BadFirst bounds and honest configuration lift.')
