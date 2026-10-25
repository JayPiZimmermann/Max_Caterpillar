#!/usr/bin/env python3
"""Freeze the complete correlated fixed-path gates, referencing their base."""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_correlated_manifest.json'
BASE=HERE/'overnight_upper_baxter_manifest.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    if a.check:
        from overnight_upper_baxter_manifest import check_manifest
        seen=set();check_manifest(DEST,seen)
        print('CORRELATED PACKAGE CHECKED',len(seen),'MANIFESTS');return
    files={BASE,Path(__file__)}
    files.update(f for f in HERE.glob('overnight_upper_correlated_*')
                 if f!=DEST and f.is_file() and f.suffix in ('.py','.md','.json','.log'))
    rows=[dict(path=str(f.relative_to(ROOT)),bytes=f.stat().st_size,sha256=digest(f)) for f in sorted(files)]
    result=dict(status='FROZEN_COMPLETE_CORRELATED_FIXED_PATH_GATES',files=rows,
        bytes=sum(r['bytes'] for r in rows),base_manifest=str(BASE.relative_to(ROOT)),
        scope='Exact finite intersection calculation. The specified local rule closes precisely the isolated-apex subspace of the fixed-path canonical input span; graph-mixed and broader cyclic states remain open.')
    DEST.write_text(json.dumps(result,indent=2)+'\n')
    print('FROZEN CORRELATED PACKAGE',len(rows),'FILES',result['bytes'],'BYTES')
if __name__=='__main__':main()
