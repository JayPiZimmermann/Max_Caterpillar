#!/usr/bin/env python3
"""A cycle family with one arbitrary extra coordinate difference in its head.

After positive-circuit tiling / one nonhinge edge, the path head is
e_root-e_apex + t(e_u-e_v) + s(e_first-e_last), with s=-1,0,1.
For fixed t this is a polynomial head enlargement, unlike arbitrary orders.
Combining it with exponentially many two-block cycle orders keeps that count
exponential, but this full-S_N probe is only a necessary control.
"""
from itertools import product
from pathlib import Path
import json,sys
import overnight_upper_weighted_paths as W


def family(n,mode):
    magnitude=int(mode.removeprefix('chord'));m=n-1;out=set()
    for root,u,v,shift,mask in product(range(m),range(m),range(m),(-1,0,1),range(1<<(m-1))):
        signature=[(int(root>=i)+magnitude*(int(u>=i)-int(v>=i))-shift-int(bool(mask>>(i-1)&1)),1)
                   for i in range(1,m)]
        out.add(W.canonical(signature))
    return sorted(out)


if __name__=='__main__':
    n=int(sys.argv[1]);mode='chord'+sys.argv[2];W.family=family;W.probe(n,mode)
    path=W.HERE/f'overnight_upper_weighted_paths_{mode}_{n}.json'
    data=json.loads(path.read_text());data['family_wrapper_sha256']=W.sha(Path(__file__))
    data['scope']='All S_N orders of cycle units with head root-apex plus one arbitrary chord shift, including all top face states; necessary full-symmetry control, not an exponential family itself.'
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
