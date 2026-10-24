"""Independent direct-equation cone check for natural8 K=4.

Uses only the standard library and the already independently audited
rational arithmetic checker. No search module or LP solver is imported.
"""
import argparse
import gzip
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import overnight_fixed_bowtie_verify as arithmetic

A=[[-1,1,0,0,0],[-1,0,1,0,0],[0,1,-1,0,0],[-1,0,0,1,0],[-1,0,0,0,1],[0,0,0,1,-1]]


def initialize():
    receipt=json.loads(Path("overnight_fixed_natural8_coverage.json").read_text())
    assert receipt["status"]=="INDEPENDENT_EXACT_NATURAL8_COVERAGE_PASS" and receipt["covering_triples"]==0
    for name,key in [("overnight_fixed_natural8_inventory.json","inventory_sha256"),("overnight_fixed_natural8_coverage_quads.json","quads_sha256"),("overnight_fixed_natural8_coverage.py","checker_sha256")]:
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==receipt[key]
    inv=json.loads(Path("overnight_fixed_natural8_inventory.json").read_text())
    arithmetic.BASES={int(z):[[Q(c) for c in b] for b in row["basis"]] for z,row in inv["flats"].items()}
    arithmetic.VALUE={S:[Q(max(sum(a[i] for i in S),0)) for a in A] for S in arithmetic.SETS}
    matrix=arithmetic.rref([[arithmetic.VALUE[S][j] for S in arithmetic.SETS[:-1]] for j in range(6)])
    piv=[next(i for i,c in enumerate(row) if c) for row in matrix];assert len(piv)==6
    ann=[]
    for free in range(30):
        if free in piv:continue
        row=[Q(0)]*30;row[free]=Q(1)
        for p,r in zip(piv,matrix):row[p]=-r[free]
        assert all(sum(row[j]*arithmetic.VALUE[S][i] for j,S in enumerate(arithmetic.SETS[:-1]))==0 for i in range(6))
        ann.append(row)
    assert len(ann)==24;arithmetic.ANN=ann
    arithmetic.RHS=[2*sum(a*(1-int(0 in S)) for a,S in zip(row,arithmetic.SETS[:-1])) for row in ann]


def case_data(zs,ds):
    blocks=[arithmetic.flat(z) for z in zs];off=[0]
    for forms,_,_ in blocks:off.append(off[-1]+len(forms))
    def equation(i):
        assert 0<=i<50;e={}
        if i<26:
            U,o=arithmetic.LOCS[i]
            for k,(z,d) in enumerate(zip(zs,ds)):
                active=len(U)==5 or z>>arithmetic.RIDX[U]&1
                if o is not None:active=active and z>>arithmetic.RIDX[U|{o}]&1
                if active:arithmetic.add(e,blocks[k][1][U],Q(d),off[k])
            return e,Q(2*(-1)**(len(U)+1))
        for k,d in enumerate(ds):arithmetic.add(e,blocks[k][2][i-26],Q(d),off[k])
        return e,arithmetic.RHS[i-26]
    dims=[len(arithmetic.BASES[z]) for z in zs];coff=[0]
    for d in dims:coff.append(coff[-1]+d)
    forms=[]
    for k,(local,_,_) in enumerate(blocks):
        forms.extend(tuple([Q(0)]*coff[k]+list(f)+[Q(0)]*(coff[-1]-coff[k+1])) for f in local)
    return equation,forms


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--partial",action="store_true");args=ap.parse_args()
    start=time.monotonic();initialize();seen={tuple(z):0 for z in json.loads(Path("overnight_fixed_natural8_coverage_quads.json").read_text())}
    with gzip.open("overnight_fixed_natural8_proof.jsonl.gz","rt") as inp:
        for line in inp:
            r=json.loads(line);zs=tuple(r["flats"]);ds=tuple(r["signs"])
            assert zs in seen and len(ds)==4 and all(d in (-1,1) for d in ds)
            bit=1<<sum((d<0)<<i for i,d in enumerate(ds));assert not seen[zs]&bit;seen[zs]|=bit
            equation,forms=case_data(zs,ds);proof=r["proof"]
            assert proof[0]=="cone" and proof[3]==[]
            arithmetic.cone(proof,equation,forms);arithmetic.COUNTS["cases"]+=1
            if arithmetic.COUNTS["cases"]%5000==0:print(json.dumps({"counts":arithmetic.COUNTS,"seconds":time.monotonic()-start}),flush=True)
    complete=all(mask==(1<<16)-1 for mask in seen.values());assert args.partial or complete
    names=["overnight_fixed_natural8_proof.jsonl.gz","overnight_fixed_natural8_inventory.json","overnight_fixed_natural8_coverage_quads.json","overnight_fixed_natural8_coverage.json","overnight_fixed_bowtie_verify.py"]
    result={"status":"INDEPENDENT_EXACT_NATURAL8_K4_EXCLUSION_PASS" if complete else "PARTIAL_PROOFS_VALID",
        "counts":arithmetic.COUNTS,"seconds":time.monotonic()-start,"hashes":{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in names},
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"All real preactivations and remainder in the natural six-feature span; generic-locality/translation bridge; not Lean"}
    Path("overnight_fixed_natural8_check"+("_partial" if args.partial else "")+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
