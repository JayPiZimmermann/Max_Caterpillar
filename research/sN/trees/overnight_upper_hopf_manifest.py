#!/usr/bin/env python3
"""Freeze the complete residue gate and its elementary uniform strengthening."""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_hopf_manifest.json';BASE=HERE/'overnight_upper_baxter_manifest.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    if a.check:
        from overnight_upper_baxter_manifest import check_manifest
        seen=set();check_manifest(DEST,seen);print('HOPF BRIDGE PACKAGE CHECKED',len(seen),'MANIFESTS');return
    files={Path(__file__),BASE}
    for stem in ('hopf_residue','hopf_locality','hopf_dense_class'):
        for suffix in ('.py','.md','.json','.log','_exit.json'):
            f=HERE/('overnight_upper_'+stem+suffix)
            if f.exists():files.add(f)
    rows=[dict(path=str(f.relative_to(ROOT)),bytes=f.stat().st_size,sha256=digest(f)) for f in sorted(files)]
    result=dict(status='FROZEN_COMPLETE_CLASS_BRIDGE_OBSTRUCTIONS',files=rows,
        bytes=sum(r['bytes'] for r in rows),base_manifest=str(BASE.relative_to(ROOT)),
        primary_replay=['research/sN/trees/overnight_upper_hopf_locality.py','research/sN/trees/overnight_upper_hopf_dense_class.py'],
        scope='The complete finite residue exclusion is superseded for the fixed graph by an arbitrary-real-head/weight two-flag proof. A uniform ascending-class theorem requires a quadratic total comparison graph. Neither excludes the global exponential family or the maximum itself.')
    DEST.write_text(json.dumps(result,indent=2)+'\n');print('FROZEN HOPF BRIDGE PACKAGE',len(rows),'FILES',result['bytes'],'BYTES')
if __name__=='__main__':main()
