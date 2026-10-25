#!/usr/bin/env python3
"""Freeze the exact reflected apex-star head gauge and independent controls."""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_head_gauge_manifest.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    if a.check:
        data=json.loads(DEST.read_text())
        for r in data['files']:
            f=ROOT/r['path']
            assert f.stat().st_size==r['bytes'] and digest(f)==r['sha256'],r['path']
        print('HEAD GAUGE PACKAGE CHECKED',len(data['files']));return
    files={Path(__file__)}
    for suffix in ('.py','.md','.json','.log','_exit.json'):
        files.add(HERE/('overnight_upper_head_gauge'+suffix))
    rows=[dict(path=str(f.relative_to(ROOT)),bytes=f.stat().st_size,sha256=digest(f)) for f in sorted(files)]
    result=dict(status='FROZEN_EXACT_REFLECTED_APEX_STAR_HEAD_GAUGE',files=rows,
        bytes=sum(r['bytes'] for r in rows),
        scope='Uniform exact head-subset realization and head-centering identity, all lower-dimensional corrections retained. No product intertwiner or all-arity simplex construction claimed.')
    DEST.write_text(json.dumps(result,indent=2)+'\n')
    print('FROZEN HEAD GAUGE PACKAGE',len(rows),'FILES',result['bytes'],'BYTES')
if __name__=='__main__':main()
