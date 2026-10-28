"""Bounded shared-parameter sign search after circuit relaxation."""
import argparse
import json
import signal
import time
from pathlib import Path
import exact_lp
from overnight_fixed_bowtie_k3 import problem,dfs


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=1200)
    ap.add_argument("--case-budget",type=int,default=60);ap.add_argument("--limit",type=int,default=1000000)
    args=ap.parse_args()
    def timeout(*_):raise TimeoutError("case budget")
    signal.signal(signal.SIGALRM,timeout)
    path=Path("overnight_fixed_bowtie_k3_dfs.jsonl");done=set()
    if path.exists():
        for line in path.read_text().splitlines():
            r=json.loads(line)
            if r["status"]!="TIMEOUT":done.add((tuple(r["flats"]),tuple(r["signs"])))
    raw=Path("overnight_fixed_bowtie_k3_circuit.jsonl").read_text()
    lines=raw.splitlines()
    if not raw.endswith("\n"):lines=lines[:-1]
    started=time.monotonic();counts={"EXCLUDED":0,"SURVIVOR":0,"TIMEOUT":0};processed=0
    with path.open("a") as out:
        for line in lines:
            r=json.loads(line)
            if r["status"]!="SURVIVOR":continue
            zs=tuple(r["flats"]);ds=tuple(r["signs"])
            if (zs,ds) in done:continue
            if processed>=args.limit or time.monotonic()-started>=args.budget:break
            t=time.monotonic();before=list(exact_lp.STATS)
            signal.alarm(min(args.case_budget,max(1,int(args.budget-(t-started)))))
            try:
                found,nodes=dfs(problem(zs,ds));status="SURVIVOR" if found else "EXCLUDED"
            except TimeoutError:status="TIMEOUT";nodes=None
            finally:signal.alarm(0)
            row={"flats":zs,"signs":ds,"status":status,"nodes":nodes,"seconds":time.monotonic()-t,
                 "lp":[a-b for a,b in zip(exact_lp.STATS,before)],"case_budget":args.case_budget}
            out.write(json.dumps(row,separators=(",",":"))+"\n");out.flush()
            counts[status]+=1;processed+=1
            if processed%50==0 or status!="EXCLUDED":print(json.dumps({"processed":processed,"counts":counts,"latest":row,"seconds":time.monotonic()-started}),flush=True)
    print(json.dumps({"status":"BATCH_COMPLETE","processed":processed,"counts":counts,"seconds":time.monotonic()-started}),flush=True)


if __name__=="__main__":main()
