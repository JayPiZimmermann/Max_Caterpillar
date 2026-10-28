#!/usr/bin/env python3
"""Full symmetric paths with independently bounded suffix-head coordinates."""
from itertools import product
from pathlib import Path
import json,sys
import overnight_upper_weighted_paths as W


def family(n,mode):
    bound=int(mode.removeprefix('alphabet'))
    return sorted({W.canonical([(h,1) for h in hs]) for hs in product(range(-bound,bound+1),repeat=n-2)})


if __name__=='__main__':
    n=int(sys.argv[1]);mode='alphabet'+sys.argv[2];W.family=family;W.probe(n,mode)
    path=W.HERE/f'overnight_upper_weighted_paths_{mode}_{n}.json'
    data=json.loads(path.read_text());data['family_wrapper_sha256']=W.sha(Path(__file__))
    data['scope']='All S_N labelings of unit-weight paths with every suffix head sum in the recorded integer alphabet; arbitrary-head necessary control, no uniform sufficiency claim.'
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
