#!/usr/bin/env python3
"""Rebuild and source-bind the research graph/cycle/forest bridge."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
MODULES = ["Leaf", "Cover", "Cycle", "Konig", "CycleCheck", "Check"]
PREFIX = "MaxCaterpillar.ExponentialPush.ForestMatching."
HEADLINES = ["MaxCaterpillar.ExponentialPush.Forest.exists_leaf"] + [PREFIX + n for n in [
    "exists_cover_matching", "cover_card_le_of_no_matching", "matching_of_no_small_cover",
    "indexedGraph_oriented_cycle", "Check.singleEdge_acyclic", "Check.exact_cycle_type",
    "Check.triangle_nonacyclic", "Check.triangle_dictionary_control"]]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(text):
    out = []; i = 0; depth = 0; quoted = False
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
            j = text.find('\n', i); i = len(text) if j < 0 else j
        elif text[i] == '"': quoted = True; i += 1
        else: out.append(text[i]); i += 1
    return ''.join(out)

def closure():
    files = {}
    def visit(p):
        r = str(p.relative_to(ROOT))
        if r in files: return
        files[r] = sha(p)
        for line in code_only(p.read_text()).splitlines():
            if line.startswith('import '):
                for module in line.split()[1:]:
                    dep = ROOT / (module.replace('.', '/') + '.lean')
                    if dep.is_file(): visit(dep)
    visit(HERE / 'Check.lean')
    visit(HERE / 'CycleCheck.lean')
    return files

before = closure()
checks = [('dependency', ['lake', 'build', 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected'])]
output_dir = ROOT / '.lake/build/lib' / REL
output_dir.mkdir(parents=True, exist_ok=True)
for name in MODULES:
    checks.append((name.lower(), ['lake', 'env', 'lean', '-j1', '-o',
        str((output_dir / (name + '.olean')).relative_to(ROOT)), str(REL / (name + '.lean'))]))
if '--run' in sys.argv:
    for label, command in checks:
        with (HERE / 'logs' / (label + '_recheck.log')).open('w') as log:
            run = subprocess.run([sys.executable, str(ROOT / 'research/sN/zulip_three/lean_small_pool.py'),
                *command], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        (HERE / 'logs' / (label + '_recheck.exit')).write_text(str(run.returncode) + '\n')
        if run.returncode: raise SystemExit('FAIL ' + label)
logs = {}
for label, _ in checks:
    assert (HERE / 'logs' / (label + '_recheck.exit')).read_text().strip() == '0', label
    p = HERE / 'logs' / (label + '_recheck.log')
    logs[str(p.relative_to(ROOT))] = sha(p)
text = (HERE / 'logs/check_recheck.log').read_text() + (HERE / 'logs/cyclecheck_recheck.log').read_text()
axioms = {}
for theorem in HEADLINES:
    m = re.search("'" + re.escape(theorem) + r"' depends on axioms: \[([^]]*)\]", text, re.S)
    assert m, theorem
    ax = sorted(x.strip() for x in m[1].split(',') if x.strip())
    assert set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}, (theorem, ax)
    axioms[theorem] = ax
for name in before:
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',
        code_only((ROOT / name).read_text()), re.M), name
after = closure()
assert before == after, 'Sources changed during verification'
for p in [Path(__file__).resolve(), ROOT/'lean-toolchain', ROOT/'lakefile.lean', ROOT/'lake-manifest.json',
          ROOT/'research/sN/zulip_three/lean_small_pool.py', HERE/'README.md', HERE/'CYCLE.md']:
    after[str(p.relative_to(ROOT))] = sha(p)
receipt = {'status':'PASS', 'state':'Lean verified research leaves; not integrated or published',
    'source_files':after, 'source_count':len(after), 'logs':logs, 'headline_axioms':axioms,
    'forbidden_construct_scan':'PASS',
    'scope':'Genuine finite SimpleGraph.IsAcyclic implies an original-vertex cover no larger than a literal matching. Nonacyclic indexed graphs yield a nonempty original index subset and consistently oriented globally zero sum of coordinate differences. Arbitrary finite n, real inputs, loops ignored and parallel indices allowed in the indexed graph.',
    'nonvacuity':'Check.lean proves singleEdge on Fin3 acyclic and applies actual leaf theorem to its explicit edge. CycleCheck.lean gives a genuine triangle and a redundant dictionary with all nine ordered pairs, including loops and reverse duplicates.',
    'limits':'These are graph and cycle identities. The actual network cycle-deletion and signed-span bridge is separate; no structural MAX obstruction or exponential lower bound is claimed here.',
    'reproduce':'python3 '+str(REL/'recheck.py')+' --run'}
(HERE/'receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS',len(after),'source hashes;',len(axioms),'standard-only axiom audits')
