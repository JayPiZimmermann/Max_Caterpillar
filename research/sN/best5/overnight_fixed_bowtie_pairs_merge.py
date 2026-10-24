"""Build a separate fixed10 K3 certificate using only seven ray equations."""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path


def main():
    replacement={}
    for line in Path("overnight_fixed_bowtie_selected_pairs.jsonl").read_text().splitlines():
        r=json.loads(line)
        if r["status"]=="EXACT_EXCLUSION":replacement[tuple(r["flats"]),tuple(r["signs"])]=r["proof"]
    for line in gzip.open("overnight_fixed_bowtie_selected_pairs_tree.jsonl.gz","rt"):
        r=json.loads(line)
        if r["status"]=="EXACT_TREE_EXCLUSION":
            key=tuple(r["flats"]),tuple(r["signs"]);assert key not in replacement
            replacement[key]=r["proof"]
    assert len(replacement)==1299;counts=Counter();path=Path("overnight_fixed_bowtie_pairs_proof.jsonl.gz")
    with gzip.open("overnight_fixed_bowtie_proof.jsonl.gz","rt") as inp,gzip.open(path,"wt") as out:
        for line in inp:
            r=json.loads(line);key=tuple(r["flats"]),tuple(r["signs"])
            if key in replacement:r["proof"]=replacement.pop(key);counts["replacement"]+=1
            p=r["proof"]
            if p[0]=="cone":assert all(i<33 for i,c in p[1])
            counts[p[0]]+=1;counts["cases"]+=1
            out.write(json.dumps(r,separators=(",",":"))+"\n")
    assert not replacement and counts["cases"]==240328 and counts["tree"]==332
    result={"status":"PAIR_RAY_PROOF_MERGED","counts":counts,"proof_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_bowtie_pairs_producer.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
