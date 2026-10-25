#!/usr/bin/env python3
"""Frozen self-contained marked-affine ear exclusion checkpoint."""
from pathlib import Path
import hashlib,json,sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_marked_manifest.json'


def paths():
    sources=['marked_manifest','marked_bundle','marked_kernel_inventory',
             'marked_kernel_probe','marked_ear_inventory','marked_ear_probe',
             'oriented_products','modular_cache','modular_cache2',
             'triangle_attachments','triangle_fixed','triangle_two_pages',
             'product_family','run']
    result=[HERE/('overnight_upper_'+s+'.py') for s in sources]
    result += [HERE/('overnight_upper_'+s+'.json') for s in
               ['marked_bundle','oriented_products','modular_cache','modular_cache2']]
    result += [HERE/'overnight_upper_marked_attachment.md',
               HERE/'all_tree_dfs/rational_identity.py']
    tags=['marked_kernel_inventory','marked_kernel_probe','marked_ear_inventory',
          'marked_ear_probe','marked_bundle_extract','marked_bundle_replay2',
          'oriented_products','modular_cache','modular_cache2']
    for tag in tags:
        result += [HERE/('overnight_upper_'+tag+'.log'),
                   HERE/('overnight_upper_'+tag+'_exit.json')]
    return sorted(set(result))


def write():
    entries=[]
    for p in paths():
        data=p.read_bytes()
        entries.append(dict(path=str(p.relative_to(ROOT)),bytes=len(data),
                            sha256=hashlib.sha256(data).hexdigest()))
    out=dict(status='FROZEN_COMPLETE_MARKED_AFFINE_EAR_EXCLUSION',files=entries,
             total_bytes=sum(e['bytes'] for e in entries),
             scope='Exact N7 failure of every marked-affine ear extension from the specified six-label two-page source span. Both lower reflection sectors and all attachment channels are included. No all-two-page or all-N exclusion and no Lean claim.',
             completed_replay_seconds=542.08,
             excluded='Historical large sampled matrices and redundant raw inventories. The compact bundle contains all source descriptions, exact relations, minor points and row digests required to rebuild the certificate. The first replay launched during re-extraction and stopped on an old-schema KeyError; replay2 is the complete fresh successful replay.',
             check='python3 research/sN/trees/overnight_upper_marked_manifest.py --check',
             replay='research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_marked_manifest.py --replay')
    DEST.write_text(json.dumps(out,indent=2)+'\n')
    print('FROZEN MARKED',len(entries),'FILES',out['total_bytes'],'BYTES',flush=True)


def check():
    out=json.loads(DEST.read_text())
    for e in out['files']:
        data=(ROOT/e['path']).read_bytes()
        assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']
    print('MARKED INTEGRITY PASS',len(out['files']),'FILES',out['total_bytes'],'BYTES',flush=True)


if __name__=='__main__':
    if '--write' in sys.argv:
        write()
    else:
        check()
        if '--replay' in sys.argv:
            import overnight_upper_marked_bundle
            overnight_upper_marked_bundle.replay()
