"""Merge the old certified cases with new 27-equation witnesses.
The independent compact checker validates every resulting case afresh.
"""
import gzip
import hashlib
import json
from pathlib import Path


def main():
    replacement={}
    for line in Path("overnight_fixed_natural8_reduced_cases.jsonl").read_text().splitlines():
        r=json.loads(line);assert r["status"]=="EXACT_EXCLUSION"
        replacement[tuple(r["flats"]),tuple(r["signs"])]=r["proof"]
    allowed=set(range(26))|{36};path=Path("overnight_fixed_natural8_compact_proof.jsonl.gz");count=changed=0
    with gzip.open("overnight_fixed_natural8_proof.jsonl.gz","rt") as inp,gzip.open(path,"wt") as out:
        for line in inp:
            r=json.loads(line);key=tuple(r["flats"]),tuple(r["signs"])
            if key in replacement:r["proof"]=replacement[key];changed+=1
            assert all(i in allowed for i,c in r["proof"][1])
            out.write(json.dumps(r,separators=(",",":"))+"\n");count+=1
    assert count==54688 and changed==len(replacement)==650
    result={"status":"COMPACT_PROOF_MERGED","cases":count,"replaced_cases":changed,
        "proof_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_natural8_compact_producer.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
