#!/usr/bin/env python3
"""Rebuild the actual cycle/forest network bridge and bind its evidence."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
LOGS = HERE / 'logs'
LOGS.mkdir(exist_ok=True)
DRIVERS = ['Check.lean', 'MatchingCoverCheck.lean']
HEADLINES = [
    'MaxCaterpillar.ExponentialPush.CycleBridge.' + name for name in [
        'matchingRepresentable_iff_coverRepresentable',
        'localMatchingObstruction_iff_no_cover_representation',
        'expanded_graph_acyclic', 'expanded_graph_le_original',
        'expanded_small_covers', 'expanded_width_le',
        'matching_card_le_cover',
        'IndependentCheck.exact_replacement_contract',
        'IndependentCheck.exact_obstruction_contract',
        'IndependentCheck.triangle_graph',
        'IndependentCheck.triangle_source_nonacyclic',
        'IndependentCheck.triangle_inner_sign_control',
        'IndependentCheck.triangle_replacement',
        'IndependentCheck.empty_cover_control',
        'IndependentCheck.one_input_obstruction_false',
    ]
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    out = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif quoted:
            if text[i] == '\\': i += 2
            elif text[i] == '"': quoted = False; i += 1
            else: i += 1
        elif text.startswith('/-', i): depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"': quoted = True; i += 1
        else: out.append(text[i]); i += 1
    return ''.join(out)


def closure():
    files = {}
    research_order = []
    production_imports = set()

    def visit(p):
        rel = str(p.relative_to(ROOT))
        if rel in files:
            return
        files[rel] = sha(p)
        for line in code_only(p.read_text()).splitlines():
            if line.startswith('import '):
                for module in line.split()[1:]:
                    dep = ROOT / (module.replace('.', '/') + '.lean')
                    if dep.is_file():
                        if rel.startswith('research/') and module.startswith('MaxCaterpillar.'):
                            production_imports.add(module)
                        visit(dep)
        if rel.startswith('research/'):
            research_order.append(rel)

    for driver in DRIVERS:
        visit(HERE / driver)
    return files, research_order, sorted(production_imports)


before, research_order, production_imports = closure()
checks = [('project_imports', ['lake', 'build', *production_imports])]
for index, rel in enumerate(research_order):
    out = ROOT / '.lake/build/lib' / Path(rel).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    checks.append((f'{index:02d}_{Path(rel).stem}',
        ['lake', 'env', 'lean', '-j1', '-o', str(out.relative_to(ROOT)), rel]))
if '--run' in sys.argv:
    for label, command in checks:
        with (LOGS / (label + '.log')).open('w') as log:
            run = subprocess.run([str(ROOT / 'scripts/lean_lock.sh'), *command],
                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        (LOGS / (label + '.exit')).write_text(str(run.returncode) + '\n')
        if run.returncode:
            raise SystemExit('FAIL ' + label)

log_hashes = {}
combined = ''
for label, _ in checks:
    assert (LOGS / (label + '.exit')).read_text().strip() == '0', label
    log = LOGS / (label + '.log')
    log_hashes[str(log.relative_to(ROOT))] = sha(log)
    combined += log.read_text() + '\n'

axioms = {}
for declaration in HEADLINES:
    matches = re.findall("'" + re.escape(declaration) +
        r"' depends on axioms: \[([^]]*)\]", combined, re.S)
    assert matches, declaration
    for match in matches:
        found = sorted(a.strip() for a in match.split(',') if a.strip())
        assert set(found) <= {'propext', 'Classical.choice', 'Quot.sound'}, (declaration, found)
        axioms[declaration] = found

for rel in before:
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',
        code_only((ROOT / rel).read_text()), re.M), rel
after, _, _ = closure()
assert before == after, 'Source changed during verification'
for p in [Path(__file__).resolve(), HERE/'README.md', HERE/'AUDIT.md', ROOT/'lean-toolchain',
          ROOT/'lakefile.lean', ROOT/'lake-manifest.json', ROOT/'scripts/lean_lock.sh']:
    after[str(p.relative_to(ROOT))] = sha(p)

receipt = {
    'status': 'PASS',
    'state': 'Lean verified isolated research declarations; no production-facade import',
    'scope': 'Actual finite normalized braid networks with arbitrary real coefficients, linear heads and braid output skips. Exact same-input-arity equivalence between matching-number-at-most-r and cover-number-at-most-r representability; exact H(N,r+1) equivalence to cover-r MAX exclusion. All-input cycle/forest replacement preserves signed aggregate cancellation and normalization.',
    'source_count': len(after),
    'source_files': after,
    'logs': log_hashes,
    'headline_axioms': axioms,
    'forbidden_construct_scan': 'PASS',
    'nonvacuity': 'Independent exact contracts plus a genuine normalized triangle with all three interaction edges and its all-real forest replacement; additional small-arity controls in Check.lean and a sharp nonempty matching/cover control in MatchingCoverCheck.lean.',
    'limits': 'Second hidden width may grow by at most 3^(number of unordered input pairs). This proves no new structural MAX exclusion and no new numerical width lower bound on its own.',
    'reproduce': 'python3 ' + str(REL/'recheck.py') + ' --run',
}
(HERE/'receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print('PASS', len(after), 'source/control hashes;', len(axioms), 'standard-only axiom audits')
