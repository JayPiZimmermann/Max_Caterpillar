#!/usr/bin/env python3
"""Rebuild and content-bind the actual uncapped total-first-width tradeoff."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
REL = HERE.relative_to(ROOT)
if '--run' in sys.argv and '--locked' not in sys.argv:
    raise SystemExit(subprocess.call([str(ROOT/'scripts/lean_lock.sh'), sys.executable,
        str(Path(__file__).resolve()), *sys.argv[1:], '--locked'], cwd=ROOT))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FEEDING = '--feeding' in sys.argv
PREFIX = 'MaxCaterpillar.OvernightConstants.TradeoffTheta.'
HEADLINES = [PREFIX+n for n in ([
    'scaled_linear_absorption', 'Feeding.affine_scaled',
    'Feeding.affine_min_tradeoff', 'Feeding.affine_quadratic_of_feeding_cap',
    'Feeding.Check.exact_raw_type', 'Feeding.Check.exact_quadratic_type',
    'Feeding.Check.actual_max_three'] if FEEDING else [
    'scaled_linear_absorption', 'affine_scaled',
    'affine_min_tradeoff', 'affine_quadratic_of_first_cap',
    'Check.exact_raw_type', 'Check.exact_scaled_type', 'Check.actual_max_three'])]
HEADLINES.append('MaxCaterpillar.OvernightConstants.Tradeoff.min_tradeoff_of_scaled')


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
    files = {}; research = []; project = set()
    def visit(path):
        key = str(path.relative_to(ROOT))
        if key in files: return
        files[key] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if not line.startswith('import '): continue
            for module in line.split()[1:]:
                dep = ROOT/(module.replace('.', '/')+'.lean')
                if dep.is_file():
                    if key.startswith('research/') and module.startswith('MaxCaterpillar.'):
                        project.add(module)
                    visit(dep)
        if key.startswith('research/'):
            research.append(key)
    visit(HERE/('FeedingMinCheck.lean' if FEEDING else 'MinCheck.lean'))
    return files, research, sorted(project)


before, research, project = closure()
logs_dir = HERE/('feeding_min_logs' if FEEDING else 'min_logs')
logs_dir.mkdir(exist_ok=True)
checks = [('project_dependencies', ['lake', 'build', *project])]
for rel in research:
    name = rel[:-5].replace('/', '_')
    out = ROOT/'.lake/build/lib'/Path(rel).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    checks.append((name, ['lake', 'env', 'lean', '-j1', '-o',
        str(out.relative_to(ROOT)), rel]))
if '--run' in sys.argv:
    for label, command in checks:
        with (logs_dir/(label+'.log')).open('w') as stream:
            result = subprocess.run(command,
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
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
after, _, _ = closure()
assert before == after, 'Sources changed during verification'
for path in [Path(__file__).resolve(), ROOT/'lean-toolchain', ROOT/'lakefile.lean',
             ROOT/'lake-manifest.json', ROOT/'scripts/lean_lock.sh',
             HERE/('FEEDING.md' if FEEDING else 'MIN.md')]:
    after[str(path.relative_to(ROOT))] = sha(path)
receipt = {
    'status':'PASS', 'state':'Lean verified isolated research declaration',
    'source_files':after, 'source_count':len(after), 'logs':logs,
    'headline_axioms':axioms, 'forbidden_construct_scan':'PASS',
    'scope': ('For every N>=3, any real affine-skip network computing actual MAX_N on all real inputs satisfies h2>=min(N^2,N^4/h1prime)/175000, where h1prime counts original W columns with at least one nonzero entry. Output-only first neurons are unrestricted.' if FEEDING else 'For every N>=3, any real affine-skip network computing actual MAX_N on all real inputs satisfies h2>=min(N^2,N^4/h1)/175000, without a first-width cap; h1 counts original total first slots.'),
    'controls': ('Expanded nine-array evaluator and literal original-column denominator; exact quadratic feeding-cap type; actual MAX3 network; zero-denominator scalar boundary.' if FEEDING else 'Expanded nine-array evaluator and uncapped exact type; arbitrary real C>=1 scale; actual MAX3 network; cubic first-width instance; zero-denominator scalar boundary.'),
    'limits':'The display uses literal real division (x/0=0). This is a research leaf, not automatically integrated by a production root.',
    'reproduce':'python3 '+str(REL/'min_recheck.py')+(' --feeding' if FEEDING else '')+' --run'}
(HERE/('feeding_min_receipt.json' if FEEDING else 'min_receipt.json')).write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS',len(after),'source/control hashes;',len(axioms),'standard-only axiom audits')
