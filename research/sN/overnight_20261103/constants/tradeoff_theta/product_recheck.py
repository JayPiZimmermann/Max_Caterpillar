#!/usr/bin/env python3
"""Reproduce the unrestricted ordinary and affine-skip width-product bounds."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
REL = HERE.relative_to(ROOT)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PREFIX = 'MaxCaterpillar.OvernightConstants.TradeoffTheta.'
HEADLINES = [PREFIX+n for n in [
    'ordinary_first_quarter', 'affine_first_quarter',
    'ordinary_width_product', 'affine_width_product',
    'ProductCheck.exact_raw_type', 'ProductCheck.exact_ordinary_type',
    'ProductCheck.actual_max_six', 'ProductCheck.actual_affine_max_fifteen']]


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
            if not line.startswith('import '): continue
            for module in line.split()[1:]:
                dep = ROOT/(module.replace('.', '/')+'.lean')
                if dep.is_file(): visit(dep)
    visit(HERE/'ProductCheck.lean')
    return files


before = closure()
logs_dir = HERE/'product_logs'
logs_dir.mkdir(exist_ok=True)
checks = [('minimum_dependency', [sys.executable, str(REL/'min_recheck.py'), '--run']),
          ('first_width_dependency', ['lake', 'build', 'MaxCaterpillar.Frontier.GeneralN'])]
for name in ['Product', 'ProductCheck']:
    out = ROOT/'.lake/build/lib'/REL/(name+'.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    checks.append((name, ['lake', 'env', 'lean', '-j1', '-o',
        str(out.relative_to(ROOT)), str(REL/(name+'.lean'))]))
if '--run' in sys.argv:
    for label, command in checks:
        with (logs_dir/(label+'.log')).open('w') as stream:
            wrapped = command if label == 'minimum_dependency' else [str(ROOT/'scripts/lean_lock.sh'), *command]
            result = subprocess.run(wrapped, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        (logs_dir/(label+'.exit')).write_text(str(result.returncode)+'\n')
        if result.returncode: raise SystemExit('FAIL '+label)
logs = {}; audit_text = ''
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
    assert set(ax) <= ALLOWED, (theorem, ax)
    axioms[theorem] = ax
for name in before:
    assert not re.search(r'\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b',
        code_only((ROOT/name).read_text()), re.M), name
after = closure()
assert before == after, 'Sources changed during verification'
for path in [Path(__file__).resolve(), HERE/'min_recheck.py', HERE/'min_receipt.json',
             ROOT/'lean-toolchain', ROOT/'lakefile.lean', ROOT/'lake-manifest.json',
             ROOT/'scripts/lean_lock.sh', HERE/'PRODUCT.md']:
    after[str(path.relative_to(ROOT))] = sha(path)
receipt = {
    'status':'PASS', 'state':'Lean verified isolated research declaration',
    'source_files':after, 'source_count':len(after), 'logs':logs,
    'headline_axioms':axioms, 'forbidden_construct_scan':'PASS',
    'scope':'Original h1*h2>=N^4/700000 with no upper-width hypothesis: ordinary real biased networks for N>=6, arbitrary real affine-skip biased networks for N>=15, both computing actual MAX_N on all real inputs.',
    'controls':'Expanded nine-array evaluator; ordinary exact type; actual MAX6 and affine MAX15 networks; first-width encoding loss 2N retained explicitly.',
    'limits':'A product bound, not an unrestricted superlinear or exponential lower bound on h2 alone. Research leaf, not automatically integrated by a production root.',
    'reproduce':'python3 '+str(REL/'product_recheck.py')+' --run'}
(HERE/'product_receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS',len(after),'source/control hashes;',len(axioms),'standard-only axiom audits')
