#!/usr/bin/env python3
"""Freeze the sparse cyclic bridges and their exact local-rule gates."""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parents[2]
DEST=HERE/'overnight_upper_baxter_manifest.json'
BASE=HERE/'overnight_upper_root_transfer_manifest.json'

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_manifest(path,seen):
    if path in seen:return
    seen.add(path);data=json.loads(path.read_text())
    for row in data['files']:
        f=ROOT/row['path']
        assert f.stat().st_size==row['bytes'] and digest(f)==row['sha256'],str(f)
    if data.get('base_manifest'):check_manifest(ROOT/data['base_manifest'],seen)

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    if a.check:
        seen=set();check_manifest(DEST,seen)
        print('BAXTER PACKAGE AND BASES CHECKED',len(seen),'MANIFESTS');return
    files={Path(__file__),BASE,HERE.parent/'best5/overnight_fixed_cross_net9_18.json'}
    for prefix in ('overnight_upper_baxter_','overnight_upper_root_incidence','overnight_upper_actual_support'):
        for f in HERE.glob(prefix+'*'):
            if f==DEST or not f.is_file() or f.suffix not in ('.py','.md','.json','.log'):continue
            files.add(f)
    records=[dict(path=str(f.relative_to(ROOT)),bytes=f.stat().st_size,sha256=digest(f)) for f in sorted(files)]
    result=dict(status='FROZEN_SPARSE_CYCLIC_BRIDGES_AND_LOCAL_RULE_GATES',
        files=records,bytes=sum(r['bytes'] for r in records),base_manifest=str(BASE.relative_to(ROOT)),
        positive_replay=['research/sN/trees/overnight_upper_baxter_bridge_check.py'],
        negative_replay=['research/sN/trees/overnight_upper_baxter_split_check.py'],
        compactness='No raw matrices or full NC7 search inventory. The compact NC7 receipt contains every supported unit/coefficient and is a complete replay seed.',
        historical_failures='Initial apex-controls, locality, max5 conversion and NC7 embedding attempts have failed log/exit records; the later successful receipts and independent replays carry the claims.',
        scope='Uniform scalar identities, graphic tiling/count lemmas and an opaque-offset no-go; exact finite N5/N7 positive top-class bridges and local-rule exclusions. No exponential all-N construction and no new Lean claim.')
    DEST.write_text(json.dumps(result,indent=2)+'\n')
    print('FROZEN BAXTER PACKAGE',len(records),'FILES',result['bytes'],'BYTES')

if __name__=='__main__':main()
