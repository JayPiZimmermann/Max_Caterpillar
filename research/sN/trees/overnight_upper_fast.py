#!/usr/bin/env python3
"""Export and control a small-memory native orbit evaluator before use."""
from pathlib import Path
import json
import math
import random
import struct
import subprocess
import sys
import time

import numpy as np
from exponential_families_batch import engine,evaluate,PRIME
import overnight_upper_probe as P
import overnight_upper_modular_probe as M

HERE=Path(__file__).parent
EXE=Path('/tmp/overnight_upper_fast')
BIN=HERE/'overnight_upper_modular_engine.bin'
POINTS=HERE/'overnight_upper_modular_points.txt'


def prepare():
    started=time.monotonic();orbits,sources=M.source_orbits('modular');n=7
    keys,offsets,forms,incidence,apices=engine(n,orbits)
    pairs,indices=np.unique(incidence.reshape(-1,2),axis=0,return_inverse=True)
    with BIN.open('wb') as f:
        f.write(struct.pack('<6Q',0x5550504552504149,n,len(forms),len(pairs),len(keys),len(orbits)))
        forms.astype('<i4').tofile(f);pairs.astype('<u4').tofile(f);indices.astype('<u4').tofile(f)
        apices.astype('u1').tofile(f);np.append(offsets,len(keys)).astype('<u8').tofile(f)
    subprocess.run(['g++','-O3','-std=c++17',str(HERE/'overnight_upper_fast.cpp'),'-o',str(EXE)],check=True)
    rng=random.Random(P.SEED);width=len(orbits);rows=width+32;points=[];rejected=0
    while len(points)<rows:
        point=[rng.randrange(1,1000000) for _ in range(n-1)];point.append(-sum(point));rng.shuffle(point)
        if np.all(np.array(point,dtype=np.int64)@forms.T%PRIME) and math.prod(point)%PRIME:points.append(point)
        else:rejected+=1
    POINTS.write_text(f'{rows} {n}\n'+''.join(' '.join(map(str,p))+'\n' for p in points))
    control=HERE/'overnight_upper_modular_fast_controls.u32';began=time.monotonic()
    subprocess.run([str(EXE),str(BIN),str(POINTS),str(control),'0','32'],check=True)
    seconds=time.monotonic()-began;native=np.fromfile(control,dtype=np.uint32).reshape(32,width+1)
    expected,unused=evaluate(n,points[:32],offsets,forms,incidence,apices)
    assert np.array_equal(native,expected)
    independent=[sum(P.dfs_value_mod((tuple(h),tuple(map(tuple,es))),points[0],PRIME) for h,es in orb)%PRIME for orb in orbits]
    independent.append(pow(math.prod(points[0])%PRIME,-1,PRIME))
    assert independent==list(map(int,native[0]))
    data=dict(status='MATRIX_GENERATION_PENDING',n=n,family='modular',orbit_columns=width,rows=rows,prime=PRIME,
              seed=P.SEED,sources=sources,points=points,rejected_points=rejected,completed_rows=0,
              producer_sha256=P.digest(Path(__file__)),cpp_sha256=P.digest(HERE/'overnight_upper_fast.cpp'),
              engine_sha256=P.digest(BIN),numpy_control_full_rows=32,independent_first_row_entries=width+1,
              native_32_rows_seconds=seconds,native_estimated_full_seconds=seconds*rows/32,
              engine_forms=len(forms),engine_factor_pairs=len(pairs),engine_units=len(keys),
              preparation_seconds=time.monotonic()-started)
    P.stem('modular').with_suffix('.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('points','sources')}),flush=True)


def generate():
    path=P.stem('modular');meta=path.with_suffix('.json');data=json.loads(meta.read_text())
    assert data['cpp_sha256']==P.digest(HERE/'overnight_upper_fast.cpp') and data['engine_sha256']==P.digest(BIN)
    target=path.with_suffix('.u32');rowbytes=(data['orbit_columns']+1)*4
    start=target.stat().st_size//rowbytes if target.exists() else 0
    if target.exists():
        with target.open('r+b') as f:f.truncate(start*rowbytes)
    count=min(data['rows']-start,max(32,int(950*32/data['native_32_rows_seconds'])))
    subprocess.run([str(EXE),str(BIN),str(POINTS),str(target),str(start),str(count)],check=True)
    complete=target.stat().st_size//rowbytes;data['completed_rows']=complete
    if complete==data['rows']:data.update(status='MATRIX_COMPLETE',matrix_sha256=P.digest(target))
    meta.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('DONE',data['status'],complete,flush=True)


if __name__=='__main__':globals()[sys.argv[1]]()
