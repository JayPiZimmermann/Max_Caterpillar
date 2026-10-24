#!/usr/bin/env python3
"""Integrity manifest and fresh exact replay for the compact N7 witness."""
from pathlib import Path
import hashlib
import json
import sys
import tempfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
MANIFEST=HERE/'overnight_upper_affine_manifest.json'
LOCAL=[
 'overnight_upper_affine_certificate.py','overnight_upper_affine_certificate_7.json',
 'overnight_upper_affine_verify.py','overnight_upper_affine_verified_7.json',
 'overnight_upper_affine_verify.log','overnight_upper_affine_verify_exit.json',
 'overnight_upper_affine_replay_7.json','overnight_upper_affine_replay.log','overnight_upper_affine_replay_exit.json',
 'overnight_upper_affine_export.log','overnight_upper_affine_export_exit.json',
 'overnight_upper_modular_residues.py','overnight_upper_modular_residues.json',
 'overnight_upper_modular_residues.log','overnight_upper_modular_residues_exit.json',
 'overnight_upper_modular_exact.py','overnight_upper_modular_exact.json',
 'overnight_upper_modular_exact.log','overnight_upper_modular_exact_exit.json',
 'overnight_upper_affine_bfs.md','overnight_upper_probe.py','overnight_upper_run.py',
 'exponential_families.py','exponential_families_probe.py','exponential_families_batch.py',
 'gluing_review.py','gluing_review_gates.py','overnight_upper_affine_manifest.py',
]
OTHER=['research/sN/cycles/cycle_fourier.py','research/sN/trees/all_tree_dfs/rational_identity.py']


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def create():
    verified=json.loads((HERE/'overnight_upper_affine_verified_7.json').read_text())
    assert verified['status']=='EXACT_TOP_IDENTITY_FROM_COMPACT_WITNESS'
    assert len(verified['completed'])==len(verified['pole_orbits'])==16
    assert verified['certificate_sha256']==sha(HERE/'overnight_upper_affine_certificate_7.json')
    for key,path in [('producer_sha256','overnight_upper_affine_verify.py'),
                     ('decoder_sha256','overnight_upper_affine_certificate.py'),
                     ('residue_checker_sha256','overnight_upper_modular_residues.py'),
                     ('rational_checker_sha256','all_tree_dfs/rational_identity.py')]:
        assert verified[key]==sha(HERE/path)
    replay=json.loads((HERE/'overnight_upper_affine_replay_7.json').read_text())
    assert replay['certificate_sha256']==verified['certificate_sha256']
    assert replay['expression_sha256']==verified['expression_sha256']
    for tag in ('affine_verify','affine_replay','affine_export','modular_residues','modular_exact'):
        exit_data=json.loads((HERE/f'overnight_upper_{tag}_exit.json').read_text())
        assert exit_data['returncode']==0 and not exit_data['timed_out']
    files=[]
    for path in [HERE/name for name in LOCAL]+[ROOT/name for name in OTHER]:
        files.append(dict(path=str(path.relative_to(ROOT)),bytes=path.stat().st_size,sha256=sha(path)))
    data=dict(status='STABLE_EXACT_RESEARCH_WITNESS_CHECKPOINT',n=7,
              claim='Exact top-class max_7 identity in the affine BFS family; finite face-dictionary sufficiency follows from the separately reviewed face-closure lemma.',
              limitations='No uniform upper bound, no width-optimal network, no Lean certificate; 170835 is the full-unit count before face corrections.',
              selected_orbits=4068,selected_units=170835,exact_terms=170836,
              required_large_artifacts='None. The fresh verifier reads only the compact certificate and these source dependencies.',
              excludes='Full inventory, native engine, sample matrices, CRT proposal caches, and unfinished research branches.',
              integrity_command=['python3','research/sN/trees/overnight_upper_affine_manifest.py','--check'],
              fresh_exact_command=['research/sN/dfs/h5-growth/venv/bin/python','research/sN/trees/overnight_upper_affine_manifest.py','--prove'],
              runtime_requirements=['Python 3','NumPy','python-flint'],
              fresh_exact_scope='Creates a new receipt in a temporary directory, so no previously completed principal-part checks are reused.',
              files=sorted(files,key=lambda x:x['path']))
    MANIFEST.write_text(json.dumps(data,indent=2)+'\n')
    print('STABLE MANIFEST',len(files),'FILES',sum(f['bytes'] for f in files),'BYTES')


def check():
    data=json.loads(MANIFEST.read_text())
    for entry in data['files']:
        path=ROOT/entry['path'];assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],entry['path']
    print('INTEGRITY PASS',len(data['files']),'FILES')


def prove():
    check()
    import overnight_upper_affine_verify as V
    with tempfile.TemporaryDirectory(prefix='max_caterpillar_affine_exact_') as directory:
        V.OUTPUT=Path(directory)/'fresh_receipt.json';V.main()
        data=json.loads(V.OUTPUT.read_text())
        assert data['status']=='EXACT_TOP_IDENTITY_FROM_COMPACT_WITNESS'
        print('FRESH EXACT PROOF PASS',data['exact_terms'],'TERMS',len(data['completed']),'POLE ORBITS')


if __name__=='__main__':
    action=sys.argv[1] if len(sys.argv)>1 else ''
    {'--check':check,'--prove':prove}.get(action,create)()
