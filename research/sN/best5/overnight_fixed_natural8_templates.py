"""Check 21 explicit inequality templates on the complete natural8 K4 cover.

No LP, archived per-case proof, or producer verdict is used. Direct exact
mixed-difference equations and the one negative-corner identity are rebuilt
by the independent arithmetic checker. All four-tuples and all signs are
enumerated, including repetitions. A template's coefficients must all be
nonpositive on the independent nonnegative absolute-value variables.
"""
import hashlib
import itertools
import json
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import overnight_fixed_natural8_verify as engine


# Locality indices are explicitly interpreted by arithmetic.LOCS. Index36
# is the negative-corner combination asserted below. Half-integral old
# witnesses have been multiplied by two. Templates are tried in a fixed
# order only to speed up the check; that order has no mathematical force.
TEMPLATES=[
    [(13,1)], [(14,1)], [(12,1)], [(18,1)], [(2,1)], [(16,1)],
    [(8,1)], [(4,1)], [(6,1)], [(24,-1)], [(25,1)],
    [(0,1),(4,-1),(16,1)],
    [(4,1),(8,-1),(14,1)], [(6,1),(8,-1),(18,1)],
    [(8,-1),(12,1),(18,1)], [(8,-1),(14,1),(16,1)],
    [(12,2),(20,2),(25,1)],
    [(13,1),(36,1)], [(14,1),(36,1)], [(24,-1),(36,1)],
    [(17,1),(36,1)],
]


def main():
    start=time.monotonic();engine.initialize();a=engine.arithmetic
    support={tuple(sorted(S)):c for c,S in zip(a.ANN[10],a.SETS[:-1]) if c}
    assert support=={(0,1):Q(-1),(0,3):Q(-1),(0,1,3):Q(1)} and a.RHS[10]==0
    quads=json.loads(Path("overnight_fixed_natural8_coverage_quads.json").read_text())
    assert len(quads)==3418 and len({tuple(z) for z in quads})==3418
    counts=Counter();hist=Counter()
    for zs in quads:
        for ds in itertools.product((1,-1),repeat=4):
            equation,_=engine.case_data(tuple(zs),ds);cache={}
            for ti,template in enumerate(TEMPLATES):
                coefficients={};rhs=Q(0)
                for i,c in template:
                    if i not in cache:cache[i]=equation(i)
                    e,r=cache[i];a.add(coefficients,e,Q(c));rhs+=c*r
                assert rhs>0
                if all(c<=0 for c in coefficients.values()):
                    uses_defect=any(i==36 for i,c in template)
                    if uses_defect:
                        assert rhs==2 and dict(template)[36]==1
                        counts["strict_defect_at_most_minus_two"]+=1
                    else:counts["locality_contradiction"]+=1
                    hist[ti]+=1;break
            else:raise AssertionError(("NO_TEMPLATE",zs,ds))
            counts["cases"]+=1
    assert counts["cases"]==54688
    names=["overnight_fixed_natural8_verify.py","overnight_fixed_bowtie_verify.py",
           "overnight_fixed_natural8_coverage.py","overnight_fixed_natural8_coverage_quads.json",
           "overnight_fixed_natural8_coverage.json"]
    result={"status":"INDEPENDENT_21_TEMPLATE_NATURAL8_K4_PASS","counts":counts,"template_histogram":hist,
            "seconds":time.monotonic()-start,"checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "hashes":{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in names},
            "scope":"Every real K4 case contradicts locality or forces signed triangle deficit <= -2; no LP or per-case proof dependency"}
    Path("overnight_fixed_natural8_templates.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
