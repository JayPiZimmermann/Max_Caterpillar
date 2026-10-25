#!/usr/bin/env python3
"""Freeze/check the completed ordered-lift and sparse-contraction package."""
from pathlib import Path
import argparse,ast,hashlib,json

HERE=Path(__file__).parent
ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_ordered_manifest.json'
STEMS=[
 'ordered_coherent','ordered_contraction','ordered_doubling',
 'ordered_product_homotopy','ordered_augmentation','ordered_undoubled',
 'ordered_normalized','ordered_sparse_homotopy','ordered_sparse_support',
 'ordered_noncrossing','ordered_noncrossing_seed','ordered_ainfty',
 'ordered_ainfty_pages','ordered_ainfty_affine','ordered_ainfty_check',
 'bst_coupling','bst_pair_states',
]
LOGS=[
 'ordered_coherent2','ordered_contraction','ordered_doubling',
 'ordered_product_homotopy','ordered_augmentation','ordered_undoubled',
 'ordered_normalized','ordered_sparse_homotopy','ordered_sparse_support2',
 'ordered_noncrossing','ordered_noncrossing_seed','ordered_ainfty_pages',
 'ordered_ainfty_affine2','ordered_ainfty_check','bst_coupling','bst_pair_states3',
]

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    if args.check:
        data=json.loads(DEST.read_text())
        for record in data['files']:
            p=ROOT/record['path']
            assert p.stat().st_size==record['bytes'] and digest(p)==record['sha256'],record['path']
        print('FROZEN ORDERED PACKAGE CHECKED',len(data['files']),'FILES',data['bytes'],'BYTES')
        return
    files={Path(__file__),HERE/'overnight_upper_run.py'}
    for stem in STEMS:
        for suffix in ('.py','.md','.json'):
            p=HERE/('overnight_upper_'+stem+suffix)
            if p.exists():files.add(p)
    for tag in LOGS:
        for suffix in ('.log','_exit.json'):
            p=HERE/('overnight_upper_'+tag+suffix)
            if p.exists():files.add(p)
    # Include all local Python dependencies, including already frozen sources.
    scanned=set()
    while True:
        pending=[p for p in files if p.suffix=='.py' and p not in scanned]
        if not pending:break
        for p in pending:
            scanned.add(p)
            for node in ast.walk(ast.parse(p.read_text())):
                names=[a.name for a in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
                for name in names:
                    for folder in (HERE,HERE/'all_tree_dfs',p.parent):
                        q=folder/(name.split('.')[0]+'.py')
                        if q.exists():files.add(q)
    records=[dict(path=str(p.relative_to(ROOT)),bytes=p.stat().st_size,sha256=digest(p)) for p in sorted(files)]
    result=dict(status='FROZEN_COMPLETED_ORDERED_LIFT_RESEARCH_PACKAGE',files=records,
                bytes=sum(r['bytes'] for r in records),
                core_notes=['research/sN/trees/overnight_upper_ordered_coherent.md',
                  'research/sN/trees/overnight_upper_ordered_augmentation.md',
                  'research/sN/trees/overnight_upper_ordered_sparse_homotopy.md',
                  'research/sN/trees/overnight_upper_ordered_ainfty.md'],
                compact_independent_replay='research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_ordered_ainfty_check.py',
                scope='Uniform coherent ordered lift and sparse graph contraction; exact finite support/CPWL obstructions. No exponential total network width and no Lean verification is claimed.',
                excluded='Large modular matrices, active searches, unrelated other-agent files. Earlier failed/superseded logs are not needed for these final receipts.')
    DEST.write_text(json.dumps(result,indent=2)+'\n')
    print('FROZEN',len(records),'FILES',result['bytes'],'BYTES')

if __name__=='__main__':main()
