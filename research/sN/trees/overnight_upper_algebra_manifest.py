#!/usr/bin/env python3
"""Freeze logarithmic and finite marked-Eulerian algebra, no active searches."""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_algebra_manifest.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    if a.check:
        data=json.loads(DEST.read_text())
        for r in data['files']:
            f=ROOT/r['path'];assert f.stat().st_size==r['bytes'] and digest(f)==r['sha256'],r['path']
        print('ALGEBRA PACKAGE CHECKED',len(data['files']));return
    files={Path(__file__)}
    for stem in ('logarithmic_states','marked_eulerian'):
        for suffix in ('.py','.md','.json','.log','_exit.json'):
            files.add(HERE/('overnight_upper_'+stem+suffix))
    rows=[dict(path=str(f.relative_to(ROOT)),bytes=f.stat().st_size,sha256=digest(f)) for f in sorted(files)]
    result=dict(status='FROZEN_LOGARITHMIC_AND_FINITE_MARKED_EULERIAN_IDENTITIES',files=rows,
        bytes=sum(r['bytes'] for r in rows),
        scope='Uniform formal identities, finite-truncation obstructions and standard-library exact controls. No geometric Hopf intertwiner or exponential network claim.')
    DEST.write_text(json.dumps(result,indent=2)+'\n')
    print('FROZEN ALGEBRA PACKAGE',len(rows),'FILES',result['bytes'],'BYTES')
if __name__=='__main__':main()
