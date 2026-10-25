#!/usr/bin/env python3
"""Freeze/check the actual exceptional-root and geometric aggregation work."""
from pathlib import Path
import argparse,hashlib,json

HERE=Path(__file__).parent;ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_root_transfer_manifest.json'
BASE=HERE/'overnight_upper_ordered_manifest.json'
STEMS=['ordered_single_facet','ordered_root_transfer','ordered_geometric_compress',
       'ordered_root_powers']

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true')
    args=p.parse_args()
    if args.check:
        data=json.loads(DEST.read_text())
        for r in data['files']:
            f=ROOT/r['path'];assert digest(f)==r['sha256'] and f.stat().st_size==r['bytes'],r['path']
        base=json.loads(BASE.read_text())
        for r in base['files']:
            f=ROOT/r['path'];assert digest(f)==r['sha256'] and f.stat().st_size==r['bytes'],r['path']
        print('ROOT TRANSFER PACKAGE AND BASE CHECKED',len(data['files']),len(base['files']))
        return
    files={Path(__file__),BASE}
    for stem in STEMS:
        for suffix in ('.py','.md','.json','.log','_exit.json'):
            f=HERE/('overnight_upper_'+stem+suffix)
            if f.exists():files.add(f)
    records=[dict(path=str(f.relative_to(ROOT)),bytes=f.stat().st_size,sha256=digest(f)) for f in sorted(files)]
    result=dict(status='FROZEN_ACTUAL_ROOT_TRANSFER_AND_GEOMETRIC_COMPRESSION',
        files=records,bytes=sum(r['bytes'] for r in records),
        base_manifest=str(BASE.relative_to(ROOT)),
        mathematical_results='Root-preserving naturality, exceptional-coface recurrence, local and product root-transfer homotopies.',
        finite_controls='Actual lifts through simplex dimension6; all lower-dimensional aggregation corrections retained.',
        resource_stop='ordered_root_powers exited1 at3GiB while expanding the fifth power on z21. Its completed log entries are measurements, not a completed uniform test.',
        scope='No exponential total-width theorem and no exact maximum network beyond the established top-class construction.')
    DEST.write_text(json.dumps(result,indent=2)+'\n')
    print('FROZEN ROOT TRANSFER',len(records),'FILES',result['bytes'],'BYTES')

if __name__=='__main__':main()
