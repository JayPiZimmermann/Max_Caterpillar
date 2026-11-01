#!/usr/bin/env python3
"""Bounded repeated-prime lifting on a fixed independent column support."""
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import sys
import time

from flint import fmpz
import overnight_upper_reconstruct as R
from overnight_upper_solution import reconstruct

HERE=Path(__file__).parent
OUTPUT=HERE/'overnight_upper_modular_multicrt.json'


def main(count):
    started=time.monotonic();source=json.loads(R.SOLUTION.read_text())
    selected=[j for j,c in enumerate(source['coefficients_mod_prime']) if c]
    modulus=source['prime'];values=[source['coefficients_mod_prime'][j] for j in selected]
    prime=1000000009;history=[];previous=None;sources=[]
    for index in range(count):
        while not fmpz(prime).is_prime():prime+=2
        path=HERE/f'overnight_upper_reconstruct_{prime}.json'
        if not path.exists():R.solve(prime)
        data=json.loads(path.read_text())
        assert data['selected_columns']==selected and data['ranks']==[len(selected)]*2
        inverse=pow(modulus,-1,prime)
        values=[a+modulus*((b-a)*inverse%prime) for a,b in zip(values,data['coefficients_mod_prime'])]
        modulus*=prime;sources.append(dict(path=path.name,sha256=R.base.digest(path)))
        bound=math.isqrt(modulus//2);cs=[reconstruct(v,modulus,bound) for v in values]
        record=dict(primes=index+2,last_prime=prime,modulus_bits=modulus.bit_length(),
                    reconstructed=sum(c is not None for c in cs),total=len(cs),
                    stable_from_previous=sum(c is not None and c==p for c,p in zip(cs,previous)) if previous is not None else None,
                    elapsed_seconds=time.monotonic()-started)
        history.append(record)
        out=dict(status='CRT_RECONSTRUCTION_INCOMPLETE',selected_columns=selected,modulus=modulus,
                 coefficients_mod_modulus=values,history=history,sources=sources,
                 source_solution_sha256=R.base.digest(R.SOLUTION),producer_sha256=R.base.digest(Path(__file__)))
        if all(c is not None for c in cs):
            out.update(status='RATIONAL_PROPOSAL_PENDING_EXACT_GATE',coefficients=list(map(str,cs)),
                       max_coefficient_bits=max(max(abs(c.numerator).bit_length(),c.denominator.bit_length()) for c in cs))
        OUTPUT.write_text(json.dumps(out,separators=(',',':'))+'\n')
        print('CRT',json.dumps(record),flush=True)
        if out['status']=='RATIONAL_PROPOSAL_PENDING_EXACT_GATE':break
        previous=cs;prime+=2
        if time.monotonic()-started>1050:break


if __name__=='__main__':main(int(sys.argv[1]))
