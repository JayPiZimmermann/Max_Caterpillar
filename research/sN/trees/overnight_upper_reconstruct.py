#!/usr/bin/env python3
"""Fixed-support multi-prime reconstruction; all positives still need exact gates."""
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import subprocess
import sys
import time

import numpy as np
from flint import nmod_mat,ctx
import overnight_upper_probe as base
from overnight_upper_solution import reconstruct

ctx.threads=1
HERE=Path(__file__).parent
SOLUTION=HERE/'overnight_upper_modular_solution.json'
ENGINE=HERE/'overnight_upper_modular_engine.bin'
POINTS=HERE/'overnight_upper_modular_points.txt'
COLS=HERE/'overnight_upper_modular_support.txt'


def solve(prime):
    started=time.monotonic();source=json.loads(SOLUTION.read_text())
    selected=[j for j,c in enumerate(source['coefficients_mod_prime']) if c]
    rows=len(selected)+32;width=len(selected)+1
    COLS.write_text(str(len(selected))+'\n'+' '.join(map(str,selected))+'\n')
    prefix=HERE/f'overnight_upper_reconstruct_{prime}'
    binary=Path(f'/tmp/overnight_upper_reconstruct_{prime}')
    subprocess.run(['g++','-O3','-std=c++17',f'-DUPPER_PRIME={prime}ULL',str(HERE/'overnight_upper_reconstruct.cpp'),'-o',str(binary)],check=True)
    subprocess.run([str(binary),str(ENGINE),str(POINTS),str(prefix.with_suffix('.u32')),str(COLS),'0',str(rows)],check=True)
    values=np.fromfile(prefix.with_suffix('.u32'),dtype=np.uint32).reshape(rows,width)
    if prime==source['prime']:
        original=np.memmap(HERE/'overnight_upper_modular_7.u32',dtype=np.uint32,mode='r',shape=(16616,16585))
        assert np.array_equal(values,original[:rows,selected+[16584]])
    matrix=nmod_mat(rows,width,prime)
    for i,row in enumerate(values):
        for j,v in enumerate(row):matrix[i,j]=int(v)
    print('FILLED',rows,width,'SECONDS',time.monotonic()-started,flush=True)
    reduced,rank=matrix.rref(inplace=True)
    pivots=[next(j for j in range(width) if reduced[i,j]) for i in range(rank)]
    out=dict(status='FIXED_SUPPORT_MODULAR_PROBE',prime=prime,selected_columns=selected,rows=rows,
             ranks=[rank-int(width-1 in pivots),rank],matrix_sha256=base.digest(prefix.with_suffix('.u32')),
             source_solution_sha256=base.digest(SOLUTION),producer_sha256=base.digest(Path(__file__)),
             cpp_sha256=base.digest(HERE/'overnight_upper_reconstruct.cpp'))
    if pivots==list(range(width-1)):
        coefficients=[int(reduced[i,width-1]) for i in range(width-1)]
        out['coefficients_mod_prime']=coefficients
        if prime==source['prime']:assert coefficients==[source['coefficients_mod_prime'][j] for j in selected]
    out['elapsed_seconds']=time.monotonic()-started
    prefix.with_suffix('.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('RANKS',out['ranks'],'SECONDS',out['elapsed_seconds'],flush=True)


def recover(primes):
    source=json.loads(SOLUTION.read_text());selected=[j for j,c in enumerate(source['coefficients_mod_prime']) if c]
    modulus=source['prime'];values=[source['coefficients_mod_prime'][j] for j in selected];sources=[]
    for prime in primes:
        path=HERE/f'overnight_upper_reconstruct_{prime}.json';data=json.loads(path.read_text())
        assert data['selected_columns']==selected and data['ranks']==[len(selected)]*2
        inverse=pow(modulus,-1,prime)
        values=[a+modulus*((b-a)*inverse%prime) for a,b in zip(values,data['coefficients_mod_prime'])]
        modulus*=prime;sources.append(dict(path=path.name,sha256=base.digest(path)))
    out=dict(status='CRT_RECONSTRUCTION_PENDING',modulus=modulus,selected_columns=selected,
             source_solution_sha256=base.digest(SOLUTION),sources=sources,attempts=[],proposals=[])
    for bound in [1,2,4,8,16,64,256,1024,4096,16384,65536,262144,1048576,4194304,16777216,math.isqrt(modulus//2)]:
        cs=[reconstruct(v,modulus,bound) for v in values];record=dict(numerator_bound=bound,reconstructed=sum(c is not None for c in cs),total=len(cs))
        if all(c is not None for c in cs):
            denominator=math.lcm(*(c.denominator for c in cs));record['common_denominator_bits']=denominator.bit_length()
            if denominator.bit_length()<256:record['common_denominator']=denominator
            out['proposals'].append(dict(**record,coefficients=list(map(str,cs))))
        out['attempts'].append(record);print(record,flush=True)
    (HERE/'overnight_upper_modular_crt.json').write_text(json.dumps(out,separators=(',',':'))+'\n')


if __name__=='__main__':
    if sys.argv[1]=='solve':solve(int(sys.argv[2]))
    else:recover(list(map(int,sys.argv[2:])))
