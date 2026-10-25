#!/usr/bin/env python3
"""Clear all denominators in the witness's three-label ordinary-cut residue."""
from collections import Counter
from pathlib import Path
import hashlib,json,sys,time
sys.path.append(str(Path(__file__).resolve().parents[1]/'dfs/h5-growth/venv/lib/python3.12/site-packages'))
from flint import fmpq,fmpq_mpoly_ctx
from overnight_uniform_doublewheel7_single import UNITS,WEIGHTS,chart,residues


def main():
    started=time.monotonic();total=Counter()
    for w,(root,edges)in zip(WEIGHTS,UNITS):
        for key,c in residues(root,edges,chart('cut',3)).items():total[key]+=w*c
    total={key:c for key,c in total.items()if c};assert len(total)==60
    common=Counter()
    for numerator,denominator in total:common|=Counter(denominator)
    ctx=fmpq_mpoly_ctx.get(('a','b','c','d','e'));variables=ctx.gens()
    linear=lambda form:sum((v*x for v,x in zip(form,variables)),ctx.constant(0))
    forms={form:linear(form)for form in common};answer=ctx.constant(0)
    for (numerator,denominator),coefficient in total.items():
        term=linear(numerator)**3*fmpq(coefficient.numerator,coefficient.denominator)
        for form,multiplicity in(common-Counter(denominator)).items():term*=forms[form]**multiplicity
        answer+=term
    assert answer==0
    data=dict(status='EXACT_COMMON_DENOMINATOR_ORDINARY_THREE_CUT_CANCELLATION',
              fraction_records=len(total),common_linear_forms=len(common),
              common_denominator_degree=sum(common.values()),zero_polynomial=True,
              seconds=time.monotonic()-started,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              scope='Completes the exact ordinary noncoordinate cut-pole cancellation for this two-term symmetric N7 witness; no statement about coordinate poles or shifted-minus poles vanishing.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data,indent=2))


if __name__=='__main__':main()
