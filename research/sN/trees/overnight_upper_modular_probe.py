#!/usr/bin/env python3
"""Reuse the controlled N7 engine for the modular-affine BFS enlargement.

The underlying balanced producer remains unchanged. Every positive still
passes its exact rational-identity gate; every exclusion requires exact
independent kernel identities in addition to the sampled augmented rank.
"""
import json
from pathlib import Path
import sys

import overnight_upper_probe as probe

HERE=Path(__file__).parent


def source_orbits(mode):
    assert mode=='modular'
    path=HERE/'overnight_upper_modular_bfs_7_family.json'
    data=json.loads(path.read_text())
    return data['orbits'],[dict(path=path.name,sha256=probe.digest(path),retained=len(data['orbits']))]


if __name__=='__main__':
    probe.source_orbits=source_orbits
    getattr(probe,sys.argv[1])('modular')
    path=probe.stem('modular').with_suffix('.json')
    data=json.loads(path.read_text())
    data['wrapper_sha256']=probe.digest(Path(__file__))
    if data['status']=='EXACT_SUBFAMILY_TOP_OBSTRUCTION':
        data['status']='EXACT_MODULAR_AFFINE_BFS_TOP_OBSTRUCTION'
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
