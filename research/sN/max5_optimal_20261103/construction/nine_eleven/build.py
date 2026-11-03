#!/usr/bin/env python3
"""Guarded, source-owned Lean build; durable per-module logs and exit codes."""
from pathlib import Path
import argparse,json,subprocess,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
POOL=ROOT/'research/sN/overnight_20261103/lean_pool.py'
def build(name):
    source=HERE/(name+'.lean')
    output=ROOT/'.lake/build/lib'/source.relative_to(ROOT).with_suffix('.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    cmd=['python3',str(POOL),'lake','env','lean','-o',str(output),str(source)]
    with (HERE/(name+'.log')).open('w') as log:
        result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    (HERE/(name+'.exit')).write_text(str(result.returncode)+'\n')
    print(json.dumps({'module':name,'exit':result.returncode,'seconds':time.monotonic()-start}),flush=True)
    if result.returncode:raise SystemExit(result.returncode)
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('names',nargs='*')
    args=parser.parse_args()
    names=args.names or ['Defs','Weights']+[p.stem for p in sorted(HERE.glob('Cells*.lean'),key=lambda p:int(p.stem[5:]))]+['Identity','Evaluation','Physical','Check']
    for name in names:build(name)
if __name__=='__main__':main()
