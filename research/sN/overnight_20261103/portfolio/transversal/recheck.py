#!/usr/bin/env python3
"""Rebuild and content-bind the raw-network support-transversal theorems."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'lean-toolchain').is_file())
REL = HERE.relative_to(ROOT)
LEAVES = ['Model', 'Bounds', 'Check']
PREFIX = 'MaxCaterpillar.Overnight.SupportTransversal.'
HEADLINES = [PREFIX + n for n in [
    'exists_braid_model', 'braidOnRetained_of_transversal',
    'normalized_braid_quadratic', 'affine_retained_quadratic',
    'conditional_affine_retained_lower_bound', 'affine_transversal_quadratic',
    'Check.raw_nine_arrays', 'Check.literal_transversal', 'Check.actual_max_three_control']]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(text):
    out = []
    i = depth = 0
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
    found = {}
    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in found: return
        found[rel] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if line.startswith('import '):
                for mod in line.split()[1:]:
                    dep = ROOT / (mod.replace('.', '/') + '.lean')
                    if dep.is_file(): visit(dep)
    visit(HERE / 'Check.lean')
    for p in [HERE/'README.md', Path(__file__).resolve(), ROOT/'lean-toolchain',
              ROOT/'lakefile.lean', ROOT/'lake-manifest.json', ROOT/'scripts/lean_lock.sh']:
        found[str(p.relative_to(ROOT))] = sha(p)
    return found

before = closure()
checks = [('project_imports', ['lake', 'build',
    'MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff',
    'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary',
    'MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.SetRestriction',
    'MaxCaterpillar.Frontier.Constructions'])]
for leaf in LEAVES:
    artifact = ROOT/'.lake/build/lib'/REL/(leaf+'.olean')
    artifact.parent.mkdir(parents=True, exist_ok=True)
    checks.append((leaf, ['lake','env','lean','-j1','-o',str(artifact),str(REL/(leaf+'.lean'))]))

if '--run' in sys.argv:
    for label, args in checks:
        log = HERE/('recheck_'+label+'.log')
        with log.open('w') as out:
            proc = subprocess.run([str(ROOT/'scripts/lean_lock.sh'), *args],
                                  cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
        (HERE/('recheck_'+label+'.exit')).write_text(str(proc.returncode)+'\n')
        if proc.returncode: raise SystemExit('FAILED '+label+'; see '+str(log.relative_to(ROOT)))

logs = {}
all_output = ''
for label, _ in checks:
    assert (HERE/('recheck_'+label+'.exit')).read_text().strip() == '0', label
    log = HERE/('recheck_'+label+'.log')
    logs[str(log.relative_to(ROOT))] = sha(log)
    all_output += log.read_text()+'\n'

axioms = {}
for name in HEADLINES:
    match = re.search("'"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]", all_output, re.S)
    assert match, name
    deps = sorted(x.strip() for x in match[1].split(',') if x.strip())
    assert set(deps) <= {'propext','Classical.choice','Quot.sound'}, (name,deps)
    axioms[name] = deps
for path in before:
    if path.endswith('.lean'):
        code = code_only((ROOT/path).read_text())
        assert not re.search(r'\b(?:sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b', code, re.M), path
after = closure()
assert before == after, 'Source or control changed during verification'
receipt = {
    'status':'PASS',
    'evidence_level':'Research-only exact Lean declarations; not a production-root integration',
    'scope':'Arbitrary real nine-array affine-skip MAX_N. If C hits each zero-bias, zero-sum first row with at least three nonzero coefficients, and m=N-|C|>=3, then original h2>=m^2/3000000. No first-width bound. The separate 4^q result explicitly assumes H(4q+1,q).',
    'driver':str(REL/'Check.lean'),
    'source_count':len(after),'source_files':after,'logs':logs,
    'headline_axioms':axioms,'forbidden_construct_scan':'PASS',
    'nonvacuity':'Literal exact MAX3(4,3) network with empty transversal; all nine-array and literal transversal contracts expanded.',
    'limitations':'Total relevant first rows are charged, including output-only rows. This does not assert a feeding-only variant or remove the structural H premise from the growing-matching consequence.',
    'reproduce':'python3 '+str(REL/'recheck.py')+' --run'}
(HERE/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('PASS',len(after),'source/control hashes;',len(axioms),'standard-only axiom audits')
