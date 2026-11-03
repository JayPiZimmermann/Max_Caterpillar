#!/usr/bin/env python3
"""Rebuild and source-bind the unconditional N²/175000 affine-skip theorem."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
MODULES = ['FallingHalf', 'FallingHalfModel', 'FallingJoint', 'SharpTwo',
    'cherry_concentration/ExactMoment', 'cherry_concentration/SecondMoment',
    'cherry_concentration/Concentration', 'cherry_concentration/Actual',
    'cherry_concentration/Theta', 'ThetaTwo', 'ThetaTwoActual', 'ThetaTwoTransfer',
    'ThetaCoverage', 'ThetaEnvelope', 'ThetaQuadratic', 'ThetaCheck']
PREFIX = 'MaxCaterpillar.OvernightConstants.Theta.'
HEADLINES = [PREFIX+n for n in ['coverage', 'envelope_le',
    'model_bound', 'normalized_quadratic', 'affine_quadratic',
    'Check.raw_nine_array_contract', 'Check.actual_joint_half_contract', 'Check.five_input_obstruction', 'Check.actual_high_rank_event_contract',
    'Check.smallest_arity_nonvacuity', 'Check.odd_large_arity_nonvacuity']]
HEADLINES += ['MaxCaterpillar.Overnight.Constants.Theta.'+n for n in [
    'high_lowRankMatchingMean_le_shifted', 'highSelectedTailMean_le_two',
    'highActualNeuron_fraction_le_two', 'conditional_finite_transfer_two_of_highShortRank_bound']]
HEADLINES += ['MaxCaterpillar.OvernightConstants.CherryConcentration.highBad_fraction_le_sixteenth']

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
    files = {}; project_imports = set()
    def visit(path):
        key = str(path.relative_to(ROOT))
        if key in files: return
        files[key] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if line.startswith('import '):
                for module in line.split()[1:]:
                    dep = ROOT/(module.replace('.', '/')+'.lean')
                    if dep.is_file():
                        if key.startswith('research/') and module.startswith('MaxCaterpillar.'):
                            project_imports.add(module)
                        visit(dep)
    visit(HERE/'ThetaCheck.lean')
    return files, project_imports

before, imports = closure()
logs_dir = HERE/'theta_logs'
logs_dir.mkdir(exist_ok=True)
out = ROOT/'.lake/build/lib'/REL
out.mkdir(parents=True, exist_ok=True)
checks = [('project_imports', ['lake', 'build', *sorted(imports)])]
for name in MODULES:
    (out/(name+'.olean')).parent.mkdir(parents=True, exist_ok=True)
    checks.append((name, ['lake', 'env', 'lean', '-j1', '-o',
        str((out/(name+'.olean')).relative_to(ROOT)), str(REL/(name+'.lean'))]))
if '--run' in sys.argv:
    for label, command in checks:
        with (logs_dir/(label.replace('/', '_')+'.log')).open('w') as stream:
            result = subprocess.run([str(ROOT/'scripts/lean_lock.sh'), *command],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        (logs_dir/(label.replace('/', '_')+'.exit')).write_text(str(result.returncode)+'\n')
        if result.returncode: raise SystemExit('FAIL '+label)
logs = {}; audit_text = ''
for label, _ in checks:
    assert (logs_dir/(label.replace('/', '_')+'.exit')).read_text().strip() == '0', label
    path = logs_dir/(label.replace('/', '_')+'.log')
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
after, _ = closure()
assert before == after, 'Sources changed during verification'
for path in [Path(__file__).resolve(), ROOT/'lean-toolchain', ROOT/'lakefile.lean',
             ROOT/'lake-manifest.json', ROOT/'scripts/lean_lock.sh',
             HERE/'ThetaCheck.md', HERE/'THETA.md']:
    after[str(path.relative_to(ROOT))] = sha(path)
receipt = {'status':'PASS', 'state':'Lean verified isolated research theorem',
    'source_files':after, 'source_count':len(after), 'logs':logs,
    'headline_axioms':axioms, 'forbidden_construct_scan':'PASS',
    'scope':'For every N>=3, every actual nine-array affine-skip two-hidden-layer real ReLU network computing MAX_N on all real inputs with total h1<=N^2 satisfies h2>=N^2/175000. Arbitrary biases and all skips are permitted. No unproved structural or probability premise.',
    'controls':'Literal nine-array evaluator and original total width; actual same-index half restriction; proved H(5,2); actual caterpillar witnesses at N=3 and N=50001.',
    'limits':'Isolated research theorem; production roots and previous published checkpoint are unchanged.',
    'reproduce':'python3 '+str(REL/'theta_recheck.py')+' --run'}
(HERE/'theta_receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('PASS', len(after), 'source/control hashes;', len(axioms), 'standard-only axiom audits')
