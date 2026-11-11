"""List the compact selected certificate closure, excluding search diagnostics.

The upstream Ethos manifest is used only for its download URLs/hashes; its
unrelated old SMT instance and old proof need not be published with this one.
Background mathematical dependencies are listed explicitly rather than
misrepresented as consequences of the arithmetic checker.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]

def main():
    manifest = json.loads((HERE/'manifest.json').read_text())
    selected = {
        HERE/p for p in (
            'README.md', 'manifest.json', 'verify_bundle.py',
            'fresh_replay_receipt.json', 'run.py', 'proof.py', 'bundle.py',
            'emit_singleton.py', 'PUBLICATION.md', 'publication_files.py',
            'audit/AUDIT.md', 'audit/check.py', 'audit/receipt.json',
            'audit/SINGLETON_AUDIT.md', 'audit/check_singleton.py',
            'audit/singleton_receipt.json', 'audit/minimal_cover.py',
            'audit/MINIMAL_COVER.md', 'audit/minimal_cover_receipt.json')}
    selected.update(HERE/p for p in ('audit/PUBLICATION_GEOMETRY.md',
        'midpoint_cover.py', 'midpoint_cover_receipt.json',
        'verify_local4_background.py', 'local4_background_replay.json'))
    for row in manifest['entries']:
        selected.update(HERE/row[k] for k in (
            'source', 'normalized_source', 'proof', 'cvc5_receipt', 'ethos_receipt'))
        selected.add((HERE/row['source']).with_suffix('.metadata.json'))
    # emit_singleton.py starts from this original formula and its metadata.
    selected.update((HERE/'case277.smt2', HERE/'case277.metadata.json'))
    runtime = {ROOT/p for p in manifest['dependencies']}
    math = {ROOT/p for p in (
        'notes/max5_exact/three_shared_model_audit.md',
        'notes/max5_exact/local4_matching_extremality_audit.md',
        'notes/max5_exact/local4_three_hyperplanes.md',
        'notes/max5_exact/local4_one_root_audit.md',
        'notes/berzins_max/max4_two_positive_free_linear_audit.md',
        'notes/max5_exact/allfive_shared_rank.md',
        'notes/max5_exact/shared_rank_audit.md',
        'research/sN/frontier5/max5_first_width_audit.md',
        'research/sN/frontier5/max5_width4_results.md',
        'research/sN/frontier5/max5_width4_quad_local_audit.md',
        'research/sN/best5/overnight_fixed_first9_paper.tex')}
    local4 = {ROOT/'research/sN/frontier5'/p for p in (
        'max5_exact_local4_one_root_germs.py',
        'max5_exact_local4_one_root_germs.smt2',
        'max5_exact_local4_one_root_germs_audit.smt2',
        'max5_exact_local4_one_root_germs_audit.proof.cpc',
        'max5_exact_local4_one_root_germs_audit.cvc5.json',
        'max5_exact_local4_one_root_germs_audit.ethos.json',
        'max5_exact_local4_one_root_independent_check.py',
        'max5_exact_local4_one_root_independent_replay.json')}
    groups = {'selected_artifacts': selected, 'runtime_dependencies': runtime,
              'background_mathematics': math, 'local4_background_certificate': local4}
    out = {'scope': 'Selected six-case proof package; prior mathematical lemmas remain explicit dependencies.',
           'original_manifest_sha256': hashlib.sha256((HERE/'manifest.json').read_bytes()).hexdigest(),
           'groups': {}}
    for label, paths in groups.items():
        out['groups'][label] = {}
        for p in sorted(paths):
            assert p.is_file(), p
            out['groups'][label][str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
    (HERE/'publication_files.json').write_text(json.dumps(out, indent=2)+'\n')
    allpaths = sorted({str(p.relative_to(ROOT)) for ps in groups.values() for p in ps})
    allpaths += [str((HERE/'publication_files.json').relative_to(ROOT)),
                 str((HERE/'publication_paths.txt').relative_to(ROOT))]
    (HERE/'publication_paths.txt').write_text('\n'.join(allpaths)+'\n')
    print(json.dumps({'files': len(allpaths), 'bytes': sum((ROOT/p).stat().st_size for p in allpaths)}))

if __name__ == '__main__':
    main()
