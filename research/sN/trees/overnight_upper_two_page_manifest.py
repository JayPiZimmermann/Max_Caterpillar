#!/usr/bin/env python3
"""Frozen compact manifest for completed two-page construction controls."""
from pathlib import Path
import hashlib, json, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DEST = HERE/'overnight_upper_two_page_manifest.json'


def files():
    sources = ['two_page_manifest', 'two_page_bundle', 'two_page_witness',
               'triangle_attachments', 'triangle_attachment_exact', 'triangle_fixed',
               'triangle_fixed_exact', 'triangle_two_pages', 'triangle_ear',
               'triangle_ear_exact', 'ear_translations', 'product_congruence',
               'product_family', 'run']
    result = [HERE/('overnight_upper_'+name+'.py') for name in sources]
    result += [HERE/('overnight_upper_'+name+'.json') for name in
               ['two_page_bundle', 'two_page_witness_6', 'two_page_witness_replay_6',
                'product_congruence']]
    result += [HERE/'overnight_upper_two_page_boundary.md',
               HERE/'overnight_upper_koszul_filling.md',
               HERE/'all_tree_dfs/rational_identity.py']
    tags = ['triangle_attachments_inventory', 'triangle_attachments',
            'triangle_attachment_exact', 'triangle_fixed', 'triangle_fixed_exact',
            'triangle_two_pages', 'triangle_ear', 'triangle_ear_exact',
            'ear_translations', 'product_congruence', 'two_page_witness',
            'two_page_bundle_replay', 'two_page_bundle_coverage']
    for tag in tags:
        result += [HERE/('overnight_upper_'+tag+'.log'),
                   HERE/('overnight_upper_'+tag+'_exit.json')]
    return sorted(set(result))


def write():
    entries = []
    for path in files():
        content = path.read_bytes()
        entries.append(dict(path=str(path.relative_to(ROOT)), bytes=len(content),
                            sha256=hashlib.sha256(content).hexdigest()))
    result = dict(status='FROZEN_COMPACT_TWO_PAGE_BOUNDARY_CHECKPOINT', files=entries,
                  total_bytes=sum(e['bytes'] for e in entries),
                  scope='Exact finite coherent-boundary identities and exclusions. No all-N exponential construction or Lean claim.',
                  excluded='Large sampled matrices and active non-ear graft/kernel-state searches. All needed selected minors, relations and positive witnesses are in two_page_bundle.json.',
                  check='python3 research/sN/trees/overnight_upper_two_page_manifest.py --check',
                  replay='research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_upper_two_page_manifest.py --replay')
    DEST.write_text(json.dumps(result, indent=2)+'\n')
    print('FROZEN', len(entries), 'FILES', result['total_bytes'], 'BYTES', flush=True)


def check():
    result = json.loads(DEST.read_text())
    for entry in result['files']:
        content = (ROOT/entry['path']).read_bytes()
        assert len(content) == entry['bytes'], entry['path']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
    print('INTEGRITY PASS', len(result['files']), 'FILES', result['total_bytes'], 'BYTES', flush=True)


if __name__ == '__main__':
    if '--write' in sys.argv:
        write()
    else:
        check()
        if '--replay' in sys.argv:
            import overnight_upper_two_page_bundle
            overnight_upper_two_page_bundle.replay()
