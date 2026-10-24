"""Independent verification restricted to the 26 localities and one ray.
Standard library and the independent arithmetic/equation checker only.
"""
import gzip
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import overnight_fixed_natural8_verify as engine


def main():
    start=time.monotonic();engine.initialize();a=engine.arithmetic
    support={tuple(sorted(S)):c for c,S in zip(a.ANN[10],a.SETS[:-1]) if c}
    assert support=={(0,1):Q(-1),(0,3):Q(-1),(0,1,3):Q(1)} and a.RHS[10]==0
    seen={tuple(z):0 for z in json.loads(Path("overnight_fixed_natural8_coverage_quads.json").read_text())};allowed=set(range(26))|{36};used=set()
    with gzip.open("overnight_fixed_natural8_compact_proof.jsonl.gz","rt") as inp:
        for line in inp:
            r=json.loads(line);zs=tuple(r["flats"]);ds=tuple(r["signs"])
            assert zs in seen and len(ds)==4 and all(d in(-1,1) for d in ds)
            bit=1<<sum((d<0)<<i for i,d in enumerate(ds));assert not seen[zs]&bit;seen[zs]|=bit
            proof=r["proof"];assert proof[0]=="cone" and proof[3]==[]
            assert all(i in allowed for i,c in proof[1]);used.update(i for i,c in proof[1])
            equation,forms=engine.case_data(zs,ds);a.cone(proof,equation,forms);a.COUNTS["cases"]+=1
    assert all(mask==(1<<16)-1 for mask in seen.values()) and a.COUNTS["cases"]==54688
    names=["overnight_fixed_natural8_compact_proof.jsonl.gz","overnight_fixed_natural8_verify.py","overnight_fixed_bowtie_verify.py","overnight_fixed_natural8_coverage.json"]
    result={"status":"INDEPENDENT_27_EQUATION_NATURAL8_K4_PASS","counts":a.COUNTS,"used_equation_indices":sorted(used),
        "seconds":time.monotonic()-start,"hashes":{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in names},
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Same complete all-real K4 domain; only the 26 locality equations and signed triangle-deficit balance are used"}
    Path("overnight_fixed_natural8_compact_check.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
