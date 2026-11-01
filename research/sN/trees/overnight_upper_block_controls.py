#!/usr/bin/env python3
"""Exact planted positive/negative controls for the memory-bounded solve."""
from fractions import Fraction as Q
from pathlib import Path
import json
import random

import numpy as np
from flint import nmod_mat
import overnight_upper_block as B

HERE=Path(__file__).parent
B.PREFIX=3
records=[]
for positive in (False,True):
    mode='block_control_positive' if positive else 'block_control_negative'
    rng=random.Random(24102479)
    columns=[[rng.randrange(-4,5) for _ in range(12)] for _ in range(6)]
    rows=[]
    for i in range(12):
        row=[columns[j][i] for j in range(5)]
        row.extend([row[0]+2*row[1],row[2]-row[3]])
        row.append(columns[0][i]+columns[4][i] if positive else columns[5][i])
        rows.append(row)
    stem=B.base.stem(mode);raw=np.array(rows,dtype=np.int64)%B.P
    raw.astype(np.uint32).tofile(stem.with_suffix('.u32'))
    data=dict(status='MATRIX_COMPLETE',n=7,orbit_columns=7,rows=12,completed_rows=12,
              matrix_sha256=B.base.digest(stem.with_suffix('.u32')))
    stem.with_suffix('.json').write_text(json.dumps(data)+'\n')
    B.prefix(mode);B.schur(mode);B.finish(mode)
    result=json.loads(stem.with_suffix('.json').read_text())
    direct=nmod_mat(raw.tolist(),B.P).rank()
    assert result['ranks']==([5,5] if positive else [5,6])
    assert direct==result['ranks'][1]
    if positive:
        cs=list(map(Q,result['coefficient_proposal']))
        assert all(sum(c*x for c,x in zip(cs,row[:-1]))==row[-1] for row in rows)
    else:
        free=result['kernel_free_columns'];vectors=result['kernel_proposals']
        for f,vector in zip(free,vectors):
            cs={j:Q(c) for j,c in vector}
            assert [cs.get(j,0) for j in free]==[int(j==f) for j in free]
            assert all(sum(c*row[j] for j,c in cs.items())==0 for row in rows)
    records.append(dict(positive=positive,ranks=result['ranks'],exact_integer_replay=True))
out=dict(status='BLOCK_ELIMINATION_PLANTED_CONTROLS_PASS',records=records,
         producer_sha256=B.base.digest(Path(__file__)),block_source_sha256=B.base.digest(Path(B.__file__)))
(HERE/'overnight_upper_block_controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
