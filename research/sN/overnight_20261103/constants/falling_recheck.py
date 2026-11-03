#!/usr/bin/env python3
"""Rebuild and source-bind the sharp actual falling-support restriction."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
MODULES = ['FallingHalf', 'FallingHalfModel', 'FallingJoint', 'FallingCheck']
PREFIX = 'MaxCaterpillar.Overnight.Constants.FallingHalf.'
HEADLINES = [PREFIX+n for n in [
    'falling_four_decay', 'half_falling_restriction', 'exists_model',
    'jointCost_decay', 'exists_joint_model', 'Check.exact_model_type',
    'Check.equality_at_seven', 'Check.equality_at_eight',
    'Check.joint_equality_at_three', 'Check.empty_control']]

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
    def visit(path):
        key = str(path.relative_to(ROOT))
        if key in files: return
        files[key] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if line.startswith('import '):
                for module in line.split()[1:]:
                    dep = ROOT/(module.replace('.', '/')+'.lean')
                    if dep.is_file(): visit(dep)
    visit(HERE/'FallingCheck.lean')
    return files

before = closure()
logs_dir = HERE/'falling_logs'
logs_dir.mkdir(exist_ok=True)
out = ROOT/'.lake/build/lib'/REL
out.mkdir(parents=True, exist_ok=True)
checks = [('dependency', ['lake', 'build',
    'MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf'])]
for name in MODULES:
    checks.append((name, ['lake', 'env', 'lean', '-j1', '-o',
        str((out/(name+'.olean')).relative_to(ROOT)), str(REL/(name+'.lean'))]))
if '--run' in sys.argv:
    for label, command in checks:
        with (logs_dir/(label+'.log')).open('w') as stream:
            result = subprocess.run([str(ROOT/'scripts/lean_lock.sh'), *command],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        (logs_dir/(label+'.exit')).write_text(str(result.returncode)+'\n')
        if result.returncode: raise SystemExit('FAIL '+label)
logs = {}
audit_text = ''
for label, _ in checks:
    assert (logs_dir/(label+'.exit')).read_text().strip() == '0', label
    path = logs_dir/(label+'.log')
    logs[str(path.relative_to(ROOT))] = sha(path)
    audit_text += path.read_text()+'\n'
axioms = {}
for theorem in HEADLINES:
    match = re.search("'"+re.escape(theorem)+r"' depends on axioms: \[([^]]*)\]", audit_text, re.S)
    assert match, theorem
    ax = sorted(x.strip() for x in match[1].split(',') if x.strip())
    assert set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}, (theorem, ax)
    axioms[theorem] = ax
for name in before:
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',
        code_only((ROOT/name).read_text()), re.M), name
after = closure()
assert before == after, 'Sources changed during verification'
for path in [Path(__file__).resolve(), ROOT/'lean-toolchain', ROOT/'lakefile.lean',
             ROOT/'lake-manifest.json', ROOT/'scripts/lean_lock.sh', HERE/'FALLING.md']:
    after[str(path.relative_to(ROOT))] = sha(path)
receipt = {'status':'PASS', 'state':'Lean verified isolated research leaves',
    'source_files':after, 'source_count':len(after), 'logs':logs,
    'headline_axioms':axioms, 'forbidden_construct_scan':'PASS',
    'scope':'Every exact translation-normalized MAX_N network admits a same-index normalized MAX_n restriction for 2n<=N with 16 times its fourth falling support moment <=105h1 and 8 times its non-braid first-row count <=h1, simultaneously on one actual model.',
    'controls':'Expanded actual model type, scalar equality at support sizes 3,7,8, and empty ambient/row-family boundary.',
    'limits':'This is a support restriction theorem, not by itself a second-hidden-width lower bound. Sharpness concerns scalar dyadic envelopes only.',
    'reproduce':'python3 '+str(REL/'falling_recheck.py')+' --run'}
(HERE/'falling_receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS', len(after), 'source/control hashes;', len(axioms), 'standard-only axiom audits')
