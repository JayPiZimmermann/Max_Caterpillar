"""Test a smaller ray-equation set for the already certified fixed10 K3 cases.

Only replacement rational witnesses count as success. A survivor refutes
neither the theorem nor the full sign-domain exclusion. Old artifacts are
read-only. Circuit inequalities retain exact rational relations.
"""
import argparse
import gzip
import hashlib
import json
import signal
import time
from pathlib import Path
import overnight_fixed_bowtie_certify as producer


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--rays",default="29")
    ap.add_argument("--budget",type=int,default=600)
    ap.add_argument("--tag",default="29")
    ap.add_argument("--limit",type=int,default=1000000)
    args=ap.parse_args();keep=set(map(int,args.rays.split(",")));assert keep<=set(range(26,48))
    start=time.monotonic();original=producer.system
    def selected(zs,ds,rays=False):
        m,offsets,rows,traces=original(zs,ds,rays)
        retain=[i for i,tr in enumerate(traces) if all(j<26 or j in keep for j in tr)]
        return m,offsets,[rows[i] for i in retain],[traces[i] for i in retain]
    producer.system=selected
    prefix="overnight_fixed_bowtie_selected_"+args.tag
    path=Path(prefix+".jsonl");done=set();counts={};processed=already=0
    if path.exists():
        for line in path.read_text().splitlines():
            r=json.loads(line);done.add((tuple(r["flats"]),tuple(r["signs"])))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")))
    signal.alarm(args.budget)
    try:
        with gzip.open("overnight_fixed_bowtie_proof.jsonl.gz","rt") as inp,path.open("a") as out:
            for line in inp:
                r=json.loads(line);p=r["proof"]
                if p[0]=="cone" and all(i<26 or i in keep for i,c in p[1]):already+=1;continue
                key=tuple(r["flats"]),tuple(r["signs"])
                if key in done:continue
                if processed>=args.limit:break
                t=time.monotonic();proof=producer.cone(*key,rays=True,usecuts=True)
                row={"flats":key[0],"signs":key[1],"status":"EXACT_EXCLUSION" if proof else "CONE_SURVIVOR",
                     "seconds":time.monotonic()-t}
                if proof:row["proof"]=proof
                out.write(json.dumps(row,separators=(",",":"))+"\n");out.flush()
                processed+=1;counts[row["status"]]=counts.get(row["status"],0)+1
                if processed%100==0:print(json.dumps({"processed":processed,"counts":counts,"seconds":time.monotonic()-start}),flush=True)
    except TimeoutError:print("DECLARED_BUDGET_REACHED",flush=True)
    finally:signal.alarm(0)
    result={"status":"SELECTED_RAY_CONE_BATCH_COMPLETE","rays":sorted(keep),"processed":processed,"already":already,
            "counts":counts,"seconds":time.monotonic()-start,
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(prefix+".json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
