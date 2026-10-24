#!/usr/bin/env python3
"""Stable checkpoint manifest for completed small exact upper-family exclusions.

The manifest checker verifies artifact integrity and completion invariants.
It is not a replacement for the rational-identity checker or the mathematical
Fourier/coordinate-deletion bridges documented in the accompanying notes.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
MANIFEST=HERE/'overnight_upper_negative_manifest.json'
JOBS=[
 ('star_heads_4','star_heads','4'),
 ('star_heads_5','star_heads','5'),
 ('star_heads_reciprocal_5','star_heads','5','reciprocal'),
 ('midpoint_4','midpoint','4'),
 ('midpoint_5','midpoint','5'),
 ('midpoint_reciprocal_4','midpoint','4','reciprocal'),
 ('joint_stars_5','joint_stars','5'),
 ('joint_stars_reciprocal_5','joint_stars','5','reciprocal'),
 ('circuit_4_h3','circuit','4','3'),
 ('circuit_5_h3','circuit','5','3'),
 ('circuit_5_h3_half_union','circuit','5','3','half_union'),
 ('circuit_5_h4','circuit','5','4'),
 ('weighted_star_5','weighted_star','5'),
 ('two_circuits_5','two_circuits','5'),
 ('two_circuits_union_5','two_circuits_union','5'),
 ('mean_tiles_5','mean_tiles','5'),
 ('mean_tiles_wide_5','mean_tiles','5','wide'),
]
DEPENDENCIES=[
 'research/sN/trees/overnight_upper_probe.py',
 'research/sN/trees/overnight_upper_run.py',
 'research/sN/trees/exponential_families_probe.py',
 'research/sN/trees/exponential_families_batch.py',
 'research/sN/trees/exponential_families.py',
 'research/sN/trees/gluing_review_gates.py',
 'research/sN/trees/gluing_review.py',
 'research/sN/trees/all_tree_dfs/rational_identity.py',
 'research/sN/cycles/cycle_fourier.py',
]
NOTES=['star_heads','circuit','broader','mean_tiles']


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def create():
    files={};receipts=[]
    def include(path,role):
        key=str(path.relative_to(ROOT));files[key]=dict(path=key,role=role,sha256=sha(path),bytes=path.stat().st_size)
    for tag,producer,*args in JOBS:
        source=HERE/f'overnight_upper_{producer}.py';receipt=HERE/f'overnight_upper_{tag}.json'
        log=HERE/f'overnight_upper_{tag}.log';exit_path=HERE/f'overnight_upper_{tag}_exit.json'
        d=json.loads(receipt.read_text());exit_data=json.loads(exit_path.read_text())
        assert d['status'].startswith('EXACT_')
        assert d['producer_sha256']==sha(source),(tag,'producer changed')
        assert exit_data['returncode']==0 and not exit_data['timed_out'],tag
        if 'kernel_vectors' in d:assert d['exact_kernel_count']==len(d['kernel_vectors'])
        if 'exact_kernel_passed' in d:assert sorted(d['exact_kernel_passed'])==list(range(len(d['kernel_vectors'])))
        for path,role in [(source,'producer'),(receipt,'exact_research_receipt'),(log,'run_log'),(exit_path,'exit_record')]:include(path,role)
        assert d['compact_producer_sha256']==sha(HERE/'overnight_upper_negative_compact.py')
        receipts.append(dict(path=str(receipt.relative_to(ROOT)),status=d['status'],arity=d['n'],ranks=d['ranks'],
                             exact_kernel_count=d.get('exact_kernel_count'),
                             reproduce=['research/sN/dfs/h5-growth/venv/bin/python',str(source.relative_to(ROOT)),*args],
                             compact_after_reproduction=['research/sN/dfs/h5-growth/venv/bin/python','research/sN/trees/overnight_upper_negative_compact.py',tag]))
    for name in NOTES:include(HERE/f'overnight_upper_{name}.md','mathematical_scope_and_bridge')
    for name in DEPENDENCIES:include(ROOT/name,'stable_runtime_dependency')
    include(Path(__file__).resolve(),'manifest_integrity_checker')
    include(HERE/'overnight_upper_negative_compact.py','modular_rank_and_compaction_checker')
    data=dict(status='FROZEN_COMPLETED_RESEARCH_CERTIFICATE_CHECKPOINT',date='2026-10-25',
              scope='Completed fixed-family exact exclusions and small positive controls; no unrestricted upper bound or Lean theorem.',
              excludes='Active balanced/BFS data, all large matrices and raw rational-row archives, sparse-basis checkpoints, native evaluator artifacts, and unfinished probes.',
              integrity_checker_scope='File hashes and finite-receipt completion invariants only; reproduction runs the exact mathematical checks.',
              receipts=receipts,files=sorted(files.values(),key=lambda x:x['path']))
    MANIFEST.write_text(json.dumps(data,indent=2)+'\n')
    print('MANIFEST',len(receipts),'RECEIPTS',len(files),'FILES',sum(x['bytes'] for x in files.values()),'BYTES')


def check():
    data=json.loads(MANIFEST.read_text())
    for entry in data['files']:
        path=ROOT/entry['path'];assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],entry['path']
    print('MANIFEST INTEGRITY PASS',len(data['files']),'FILES')


if __name__=='__main__':check() if len(sys.argv)>1 and sys.argv[1]=='--check' else create()
