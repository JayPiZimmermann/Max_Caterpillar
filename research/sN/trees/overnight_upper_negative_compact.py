#!/usr/bin/env python3
"""Compact completed exact receipts after independently checking modular ranks.

Frequency points and exact coefficient/kernel witnesses remain. Original
rational matrices are deterministically hashed and archived outside the small
checkpoint; the recorded producers regenerate them. No active probe is touched.
"""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import hashlib
import json
import sys

from flint import nmod_mat
from overnight_upper_negative_manifest import JOBS

HERE=Path(__file__).parent
PRIME=1000003


def sha(data):return hashlib.sha256(data).hexdigest()


def compact(tag):
    path=HERE/f'overnight_upper_{tag}.json';raw=path.read_bytes();data=json.loads(raw)
    if 'rational_rows' not in data:
        assert data['compact_producer_sha256']==sha(Path(__file__).read_bytes());return
    assert data['status'].startswith('EXACT_')
    rational=data.pop('rational_rows');rows=[]
    for row in rational:
        values=[]
        for value in row:
            q=Q(value);values.append(q.numerator%PRIME*pow(q.denominator%PRIME,-1,PRIME)%PRIME)
        rows.append(values)
    ranks=[nmod_mat([r[:-1] for r in rows],PRIME).rank(),nmod_mat(rows,PRIME).rank()]
    assert ranks==data['ranks'],(tag,ranks,data['ranks'])
    if 'kernel_vectors' in data:
        free=data['kernel_free_columns'];assert len(free)==len(data['kernel_vectors'])
        for f,raw_vector in zip(free,data['kernel_vectors']):
            vector={j:Q(c) for j,c in raw_vector};assert len(vector)==len(raw_vector)
            assert [vector.get(j,0) for j in free]==[int(j==f) for j in free]
            modular={j:c.numerator%PRIME*pow(c.denominator%PRIME,-1,PRIME)%PRIME for j,c in vector.items()}
            assert all(sum(row[j]*c for j,c in modular.items())%PRIME==0 for row in rows)
        assert len(rows[0])-1-len(free)==ranks[0]
    if 'coefficients' in data:
        coefficients=[Q(c) for c in data['coefficients']]
        modular=[c.numerator%PRIME*pow(c.denominator%PRIME,-1,PRIME)%PRIME for c in coefficients]
        assert all((sum(c*x for c,x in zip(modular,row[:-1]))-row[-1])%PRIME==0 for row in rows)
    archive_dir=HERE/'overnight_upper_negative_raw';archive_dir.mkdir(exist_ok=True)
    archive=archive_dir/(path.name+'.'+sha(raw)[:16]+'.gz')
    if not archive.exists():archive.write_bytes(gzip.compress(raw,compresslevel=9,mtime=0))
    else:assert gzip.decompress(archive.read_bytes())==raw
    data.update(modular_prime=PRIME,modular_rows=rows,modular_ranks=ranks,
                rational_rows_count=len(rational),rational_rows_sha256=sha(json.dumps(rational,separators=(',',':')).encode()),
                raw_receipt_sha256=sha(raw),raw_archive=str(archive.relative_to(HERE)),
                compact_producer_sha256=sha(Path(__file__).read_bytes()),
                compact_scope='Stored exact evaluation rows replaced by checked modular images; exact coefficient witnesses and all frequency points retained.')
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('COMPACT',tag,len(raw),'TO',path.stat().st_size,'RANKS',ranks,flush=True)


if __name__=='__main__':
    for tag in ([sys.argv[1]] if len(sys.argv)>1 else [job[0] for job in JOBS]):compact(tag)
