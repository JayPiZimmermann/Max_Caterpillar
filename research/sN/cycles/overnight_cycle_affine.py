#!/usr/bin/env python3
"""Affine closure of fixed-cycle units and every top-dimensional face state.

The family has O(poly(N)*5**N) descriptions at every arity. Span claims
require exact gates; finite-field ranks alone are diagnostics.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,itertools,json,math,random,struct,subprocess,sys,time

HERE=Path(__file__).resolve().parent
TREES=HERE.parent/'trees'
sys.path.insert(0,str(TREES))
from cycle_fourier import family,permute,tree_value,chamber_value
from exponential_families_batch import engine,evaluate,PRIME
from exponential_families_probe import ratrec,exact_expression
from rational_identity import Verifier,add


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def stem(n):return HERE/f'overnight_cycle_affine_{n}'
def group(n):return [tuple((a*i+b)%n for i in range(n)) for a in range(n) if math.gcd(a,n)==1 for b in range(n)]


def inventory(n):
    started=time.monotonic();base=family(n);G=group(n);representatives={}
    for key,(apex,atoms) in base.items():
        images=[permute(key,pi) for pi in G]
        representative=min(images)
        if representative in representatives:continue
        pi=G[images.index(representative)]
        representatives[representative]=tuple(permute(atom,pi) for atom in atoms)
    columns=[];units=[]
    for key in sorted(representatives):
        images={}
        for pi in G:
            unit=permute(key,pi)
            images.setdefault(unit,tuple(permute(atom,pi) for atom in representatives[key]))
        units.append(sorted(images))
        columns.append([atom for unit in sorted(images) for atom in images[unit]])
    data=dict(status='EXACT_FAMILY_ENUMERATION_NO_SPAN_CLAIM',n=n,group_order=len(G),
              base_units=len(base),orbit_count=len(columns),unit_count=sum(map(len,units)),
              atom_occurrences=sum(map(len,columns)),units=units,columns=columns,
              producer_sha256=sha(Path(__file__)),cycle_source_sha256=sha(HERE/'cycle_fourier.py'),
              seconds=time.monotonic()-started)
    stem(n).with_suffix('.family.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('units','columns')}),flush=True)


def load(n):
    p=stem(n).with_suffix('.family.json');data=json.loads(p.read_text())
    columns=[[(tuple(h),tuple(map(tuple,es))) for h,es in c] for c in data['columns']]
    return data,columns


def prepare(n):
    import numpy as np
    started=time.monotonic();data,columns=load(n);width=len(columns)
    keys,offsets,forms,incidence,apices=engine(n,columns)
    pairs,indices=np.unique(incidence.reshape(-1,2),axis=0,return_inverse=True)
    binary=stem(n).with_suffix('.bin')
    with binary.open('wb') as f:
        f.write(struct.pack('<6Q',0x5550504552504149,n,len(forms),len(pairs),len(keys),width))
        forms.astype('<i4').tofile(f);pairs.astype('<u4').tofile(f);indices.astype('<u4').tofile(f)
        apices.astype('u1').tofile(f);np.append(offsets,len(keys)).astype('<u8').tofile(f)
    exe='/tmp/overnight_cycle_affine_engine'
    subprocess.run(['g++','-O3','-std=c++17',str(TREES/'overnight_upper_fast.cpp'),'-o',exe],check=True)
    rng=random.Random(2026102507+n);points=[]
    while len(points)<width+32:
        p=[rng.randrange(1,1000000) for _ in range(n-1)];p.append(-sum(p));rng.shuffle(p)
        if np.all(np.array(p,dtype=np.int64)@forms.T%PRIME) and math.prod(p)%PRIME:points.append(p)
    pointfile=stem(n).with_suffix('.points.txt')
    pointfile.write_text(f'{len(points)} {n}\n'+''.join(' '.join(map(str,p))+'\n' for p in points))
    control=stem(n).with_suffix('.control.u32')
    subprocess.run([exe,str(binary),str(pointfile),str(control),'0','4'],check=True)
    got=np.fromfile(control,dtype=np.uint32).reshape(4,width+1)
    expected,_=evaluate(n,points[:4],offsets,forms,incidence,apices)
    assert np.array_equal(got,expected)
    # Independent chamber integration checks the cycle tiling, not only its evaluator.
    chamber_checks=0
    for j in sorted(set([0,width//3,2*width//3,width-1])):
        unit=data['units'][j][0];unit=(tuple(unit[0]),tuple(map(tuple,unit[1])))
        key_columns=columns[j]
        # Each orbit's atoms are grouped by sorted unit, so the first block belongs to this unit.
        count=n-1 if len(unit[1])==n-1 else 1
        apex,=set(range(n))-{v for e in unit[1] for v in e}
        for point in points:
            try:
                value=sum((tree_value(k,apex,point) for k in key_columns[:count]),Q(0))
                independent=chamber_value(unit,point)
            except ZeroDivisionError:continue
            assert value==independent,(j,value,independent)
            chamber_checks+=1;break
        else:raise AssertionError('no regular chamber control')
    result=dict(status='NATIVE_CONTROLS_PASS',n=n,columns=width,rows=len(points),prime=PRIME,
                family_sha256=sha(stem(n).with_suffix('.family.json')),binary_sha256=sha(binary),
                engine_source_sha256=sha(TREES/'overnight_upper_fast.cpp'),points=points,
                native_numpy_full_rows=4,independent_chamber_controls=chamber_checks,
                producer_sha256=sha(Path(__file__)),seconds=time.monotonic()-started)
    stem(n).with_suffix('.prepare.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='points'}),flush=True)


def generate(n):
    meta=json.loads(stem(n).with_suffix('.prepare.json').read_text());binary=stem(n).with_suffix('.bin')
    assert sha(binary)==meta['binary_sha256']
    subprocess.run(['/tmp/overnight_cycle_affine_engine',str(binary),str(stem(n).with_suffix('.points.txt')),str(stem(n).with_suffix('.u32'))],check=True,timeout=900)


def solve(n):
    import numpy as np
    from flint import nmod_mat
    started=time.monotonic();meta=json.loads(stem(n).with_suffix('.prepare.json').read_text())
    width=meta['columns'];raw=np.fromfile(stem(n).with_suffix('.u32'),dtype=np.uint32).reshape(-1,width+1)
    assert len(raw)==meta['rows']
    assert raw.size<=40000000,'use a bounded block solve for a larger matrix'
    m=nmod_mat(raw.tolist(),PRIME);rr,rank=m.rref()
    pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)]
    target=width in pivots
    result=dict(status='MODULAR_SPAN_DIAGNOSTIC',n=n,columns=width,rows=len(raw),prime=PRIME,
                ranks=[rank-int(target),rank],pivots=pivots,matrix_sha256=sha(stem(n).with_suffix('.u32')),
                producer_sha256=sha(Path(__file__)),seconds=time.monotonic()-started)
    if not target:
        cs=[Q(0)]*width;failed=[]
        for i,j in enumerate(pivots):
            c=ratrec(int(rr[i,width]),PRIME)
            if c is None:failed.append(j)
            else:cs[j]=c
        result.update(modular_coefficients=[[j,int(rr[i,width])] for i,j in enumerate(pivots) if rr[i,width]],
                      reconstruction_failures=failed)
        if not failed:result['rational_coefficients']=list(map(str,cs))
    stem(n).with_suffix('.rank.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('pivots','modular_coefficients','rational_coefficients','reconstruction_failures')}),flush=True)
    if not target and not result['reconstruction_failures']:
        _,columns=load(n);checker=Verifier(budget=180)
        ok=checker.check(exact_expression(n,columns,cs))
        result.update(status='EXACT_TOP_IDENTITY' if ok else 'RATIONAL_PROPOSAL_FAILED_EXACT_GATE',symbolic_calls=checker.calls)
        stem(n).with_suffix('.rank.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
        print(result['status'],flush=True)


if __name__=='__main__':globals()[sys.argv[1]](int(sys.argv[2]))
