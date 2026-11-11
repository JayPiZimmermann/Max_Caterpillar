#!/usr/bin/env python3
"""Read-only inventory of the frozen 2026-11-02 research checkpoint.

Writes only this audit directory. It neither rebuilds/mutates a producer nor
copies, stages, commits, or pushes publication files.
"""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PUBLIC = Path('/tmp/max4-proof-publication-20261102')
BASE = Path('research/sN/exponential_push_20261102')
RECEIPTS = [
    'structural/receipt.json', 'structural/finite_index_receipt.json',
    'forest_matching/receipt.json',
    'ridge_annihilator/no_ridge_sum_receipt.json',
    'ridge_annihilator/actual_rank_receipt.json',
    'invariants/receipt.json', 'invariants/ridge_audit/receipt.json',
    'general_rows/receipt.json', 'counting/MatchingMoment.receipt.json',
]
HASH_MAPS = {
    'project_import_source_hashes', 'control_hashes', 'source_hashes',
    'source_files', 'logs', 'source_and_control_sha256',
    'lean_project_source_hashes', 'artifact_hashes', 'sha256', 'artifacts',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


strip_path = ROOT / 'research/sN/jensen_bound/star_obstruction/star_obstruction_receipt.py'
strip_node = next(n for n in ast.parse(strip_path.read_text()).body
                  if isinstance(n, ast.FunctionDef) and n.name == 'strip_comments')
strip_ns = {}
exec(compile(ast.Module(body=[strip_node], type_ignores=[]), str(strip_path), 'exec'), strip_ns)
code_only = strip_ns['strip_comments']

files = {}
expected = {}
receipts = []
issues = []
binary_artifacts = []


def add(rel, reason, wanted=None):
    rel = str(rel)
    path = ROOT / rel
    if not path.is_file():
        issues.append({'kind': 'missing', 'path': rel, 'reason': reason})
        return
    digest = sha(path)
    if wanted is not None:
        expected.setdefault(rel, set()).add(wanted)
        if digest != wanted:
            issues.append({'kind': 'hash_drift', 'path': rel,
                           'expected': wanted, 'actual': digest, 'reason': reason})
    if rel.startswith('.lake/'):
        binary_artifacts.append({'path': rel, 'sha256': digest,
                                 'expected': wanted, 'reason': reason})
        return
    if path.suffix in {'.pdf', '.olean', '.ilean'}:
        issues.append({'kind': 'unexpected_binary', 'path': rel, 'reason': reason})
        return
    record = files.setdefault(rel, {'sha256': digest, 'reasons': []})
    if reason not in record['reasons']:
        record['reasons'].append(reason)


for receipt_name in RECEIPTS:
    rel = BASE / receipt_name
    path = ROOT / rel
    data = json.loads(path.read_text())
    add(rel, 'receipt')
    before = len(issues)
    local_bindings = 0
    for key in HASH_MAPS:
        values = data.get(key)
        if not isinstance(values, dict):
            continue
        for name, digest in values.items():
            if not isinstance(digest, str) or not re.fullmatch(r'[0-9a-f]{64}', digest):
                continue
            bound = rel.parent / name if key == 'artifact_hashes' else Path(name)
            add(bound, str(rel) + ':' + key, digest)
            local_bindings += 1
    for label, check in data.get('checks', {}).items():
        if 'log_sha256' in check:
            add(rel.parent / (label + '.log'), str(rel) + ':check_log', check['log_sha256'])
            add(rel.parent / (label + '.exit'), str(rel) + ':checker_exit_input')
            local_bindings += 1
    artifact = data.get('artifact')
    if isinstance(artifact, dict) and 'path' in artifact and 'sha256' in artifact:
        add(artifact['path'], str(rel) + ':artifact', artifact['sha256'])
    if 'prior_structural_receipt_sha256' in data:
        add(BASE / 'structural/receipt.json', str(rel) + ':prior_receipt',
            data['prior_structural_receipt_sha256'])
    receipts.append({'path': str(rel), 'sha256': sha(path),
                     'recorded_status': data.get('status', data.get('success')),
                     'scope': data.get('scope'), 'binding_count': local_bindings,
                     'issues': issues[before:]})

# Persist all receipt-bound log exit inputs as well. They are not mathematical
# source evidence, but several read-only receipt commands require these files.
for rel in list(files):
    if rel.endswith('.log') and (ROOT / rel).with_suffix('.exit').is_file():
        add(str(Path(rel).with_suffix('.exit')), 'existing corresponding log exit input')

# Controls used by verifier programs but not included in every old receipt.
for rel in [
    'lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
    'scripts/verify.py', 'scripts/lean_lock.sh',
    'research/sN/zulip_three/lean_small_pool.py',
    'research/sN/jensen_bound/star_obstruction/star_obstruction_receipt.py',
    str(BASE / 'general_rows/adaptive_offset.log'),
    str(BASE / 'general_rows/adaptive_offset.exit'),
    str(BASE / 'ridge_annihilator/finite_difference.md'),
]:
    add(rel, 'explicit reproducibility/support file; current snapshot')

# Check a complete local source import closure independently of each producer.
# MatchingMoment's older diagnostic receipt binds only its direct import;
# this records its full project source closure without changing that receipt.
pending = [rel for rel in files if rel.endswith('.lean')]
visited = set()
while pending:
    rel = pending.pop()
    if rel in visited:
        continue
    visited.add(rel)
    code = code_only((ROOT / rel).read_text())
    forbidden = re.search(r'\b(?:sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool)\b|'
                          r'^\s*(?:private\s+)?(?:axiom|unsafe)\b', code, re.M)
    if forbidden:
        issues.append({'kind': 'forbidden_lean_construct', 'path': rel,
                       'match': forbidden.group(0)})
    for line in code.splitlines():
        if line.strip().startswith('import '):
            for module in line.strip()[7:].split():
                dep = module.replace('.', '/') + '.lean'
                if (ROOT / dep).is_file():
                    add(dep, 'independent project import closure from ' + rel)
                    pending.append(dep)

copy_new = []
copy_changed = []
already_identical = []
for rel, record in files.items():
    public = PUBLIC / rel
    if not public.is_file():
        record['publication_state'] = 'new'
        copy_new.append(rel)
    elif sha(public) != record['sha256']:
        record['publication_state'] = 'changed'
        record['publication_sha256'] = sha(public)
        copy_changed.append(rel)
    else:
        record['publication_state'] = 'identical'
        already_identical.append(rel)

for rel, versions in expected.items():
    if len(versions) > 1:
        issues.append({'kind': 'conflicting_receipt_hashes', 'path': rel,
                       'hashes': sorted(versions)})

git = lambda *args: subprocess.check_output(['git', *args], cwd=PUBLIC, text=True).strip()
report = {
    'scope': 'Read-only publication inventory; no producer rebuilt and no files copied/staged/pushed.',
    'publication_head': git('rev-parse', 'HEAD'),
    'publication_status': git('status', '--short'),
    'remote_head': git('ls-remote', 'origin', 'refs/heads/proof/quadratic-second-width-20261102'),
    'receipts': receipts, 'issues': issues,
    'files': dict(sorted(files.items())),
    'copy_new': sorted(copy_new), 'copy_changed': sorted(copy_changed),
    'already_identical_count': len(already_identical),
    'checked_local_binary_artifacts_not_for_publication': binary_artifacts,
    'lean_source_count': len(visited),
    'excluded': [
        'All .olean/.ilean, PDF files, unfinished degree_two and dictionary_bridge sources.',
        'Root exponential_push_20261102/README.md awaits a current parent-owned status rewrite.',
        'Countersearch aggregate receipt is not ready: verifier hash drift and unfinished signed_fast dependency; separate audit pending.',
        'Source scan is not a new Lean kernel run or production-root promotion.',
    ],
    'reproducibility_limits': [
        'MatchingMoment has a diagnostic receipt and copied-source exact driver; its full project import closure is independently inventoried here, not newly rebuilt.',
        'Structural receipt scripts inspect recorded checks; rebuild the named leaves/drivers first to create fresh evidence.',
        'General-rows and invariant helper scripts rely on project imports already being built; use the recorded toolchain and normal project dependency build first.',
        'Finite numerical/analytic counterexample notes retain their stated scope; they are not new general H(k,q) Lean theorems.',
    ],
}
(HERE / 'selection.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
(HERE / 'copy_candidates.txt').write_text('\n'.join(sorted(copy_new + copy_changed)) + '\n')
print(json.dumps({'issues': issues, 'files': len(files), 'new': len(copy_new),
                  'changed': len(copy_changed), 'identical': len(already_identical),
                  'lean_sources': len(visited), 'receipts': len(receipts)}, indent=2))
