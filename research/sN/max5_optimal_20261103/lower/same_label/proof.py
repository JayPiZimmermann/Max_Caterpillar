"""CPC/Ethos replay wrapper for new same-label models.

The unchanged existing arithmetic auditor owns normalization and checking.
Only its output-directory variable is redirected to this task directory;
its pinned checker/dependency manifest remains the original one.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib
import json
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OLD=ROOT/'research/sN/frontier5'

def main():
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['produce','replay'])
    p.add_argument('index',type=int)
    p.add_argument('--budget',type=int,default=90)
    p.add_argument('--row-gauge',action='store_true')
    p.add_argument('--singleton',action='store_true')
    p.add_argument('--branch',choices=['pp','pn','np','nn'])
    p.add_argument('--unit-normal',action='store_true')
    a=p.parse_args()
    sys.path.insert(0,str(OLD))
    auditor=importlib.import_module('max5_exact_one_shared_proof_audit')
    auditor.HERE=HERE
    suffix='_row' if a.row_gauge else ''
    assert not (a.row_gauge and a.singleton)
    if a.singleton: suffix='_single'
    if a.branch:
        assert a.singleton
        suffix+='_'+a.branch
    if a.unit_normal:
        assert not (a.row_gauge or a.singleton or a.branch)
        suffix='_unit'
    source=HERE/f'case{a.index}{suffix}.smt2'
    meta=json.loads(source.with_suffix('.metadata.json').read_text())
    assert hashlib.sha256(source.read_bytes()).hexdigest()==meta['source_sha256']
    restored=None
    if a.mode=='replay':
        receipt=json.loads(source.with_name(source.stem+'_audit').with_suffix('.cvc5.json').read_text())
        raw=HERE/receipt['proof']
        if not raw.exists():
            data=gzip.decompress(raw.with_suffix(raw.suffix+'.gz').read_bytes())
            assert hashlib.sha256(data).hexdigest()==receipt['proof_sha256']
            raw.write_bytes(data)
            restored=raw
    try:
        (auditor.produce if a.mode=='produce' else auditor.replay)(source,a.budget)
    finally:
        if restored is not None: restored.unlink()

if __name__=='__main__':
    main()
