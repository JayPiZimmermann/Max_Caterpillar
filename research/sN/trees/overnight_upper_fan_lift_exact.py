#!/usr/bin/env python3
"""Exact rational ranks of the complete, finite fan chamber systems."""
from pathlib import Path
import hashlib,json,sys,time
from flint import fmpq_mat,ctx

HERE=Path(__file__).parent
ctx.threads=1


def main(n):
    started=time.monotonic();source=HERE/f'overnight_upper_fan_lift_{n}.json';data=json.loads(source.read_text());rows=data['integer_rows']
    ordinary=fmpq_mat([r[:-1] for r in rows]).rank();augmented=fmpq_mat(rows).rank()
    assert [ordinary,augmented]==data['ranks']
    out=dict(status='EXACT_CHAMBER_RANKS',n=n,ranks=[ordinary,augmented],rows=len(rows),columns=len(rows[0])-1,
             conclusion='The target is outside this precise bounded fan-extension span.' if augmented>ordinary else 'The target belongs to this finite symmetric span.',
             source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
    (HERE/f'overnight_upper_fan_lift_exact_{n}.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)


if __name__=='__main__':main(int(sys.argv[1]))
