"""Independent fixed10 K3 verification with only 26+7 equations.

Imports the old independent exact checker, not a producer or LP solver.
Rows33..47 are replaced by zero equations before any proof is checked.
Thus no witness or compressed tree system can use the omitted equations.
"""
import gzip
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import overnight_fixed_bowtie_verify as a


def main():
    start=time.monotonic();a.initialize()
    # The retained annihilator rows depend only on singletons and pairs.
    assert all(len(S)<=2 for row in a.ANN[:7] for S,c in zip(a.SETS[:-1],row) if c)
    expected={tuple(z):0 for z in json.loads(Path("overnight_fixed_bowtie_coverage_triples.json").read_text())}
    with gzip.open("overnight_fixed_bowtie_pairs_proof.jsonl.gz","rt") as inp:
        for line in inp:
            r=json.loads(line);zs=tuple(r["flats"]);ds=tuple(r["signs"])
            assert zs in expected and len(ds)==3 and all(d in(-1,1) for d in ds)
            bit=1<<sum((d<0)<<i for i,d in enumerate(ds));assert not expected[zs]&bit;expected[zs]|=bit
            direct,forms,coff=a.case_data(zs,ds)
            def equation(i):
                assert 0<=i<48
                return direct(i) if i<33 else ({},Q(0))
            p=r["proof"]
            if p[0]=="cone":
                assert all(i<33 for i,c in p[1]);a.cone(p,equation,forms)
            else:
                assert p[0]=="tree";a.tree(p,equation,forms,coff)
            a.COUNTS["cases"]+=1
            if a.COUNTS["cases"]%10000==0:print(json.dumps({"counts":a.COUNTS,"seconds":time.monotonic()-start}),flush=True)
    assert all(v==255 for v in expected.values()) and a.COUNTS["cases"]==240328
    names=["overnight_fixed_bowtie_pairs_proof.jsonl.gz","overnight_fixed_bowtie_verify.py",
           "overnight_fixed_bowtie_coverage.json","overnight_fixed_bowtie_inventory.json",
           "overnight_fixed_bowtie_coverage_triples.json","netB_10_6.json"]
    result={"status":"INDEPENDENT_33_EQUATION_FIXED10_K3_PASS","counts":a.COUNTS,"seconds":time.monotonic()-start,
            "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "hashes":{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in names},
            "scope":"Original complete all-real fixed10 K3 domain; only 26 locality and seven singleton/pair-ray equations; mathematical model bridge, not Lean"}
    Path("overnight_fixed_bowtie_pairs_check.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
