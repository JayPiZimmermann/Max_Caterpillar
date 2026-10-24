"""Direct rational cone certificates for the natural8 K=4 cases.
Every witness uses the unreduced 26 locality and 24 ray equations.
No earlier search verdict is read or trusted.
"""
import argparse
import contextlib
import functools
import gzip
import hashlib
import itertools
import json
import signal
import time
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_natural8_k4 import FLATS,SETS,REL,VR,TARGET,data
from overnight_fixed_k2 import canonical
from overnight_fixed_k2_certify import certified_feasible

LOCS=[(U,o) for U in REL if len(U)==3 for o in range(5) if o not in U]+[(U,None) for U in SETS if len(U) in (4,5)]


@functools.lru_cache(None)
def flat(z):
    B=[[Q(c) for c in b] for b in FLATS[z]["basis"]]
    forms=sorted({f for S in SETS[:-1] if (f:=canonical(tuple(sum(a*b for a,b in zip(VR[S],v)) for v in B))[0]) is not None})
    ix={f:i for i,f in enumerate(forms)};_,cubes,rays=data(z)
    return forms,{U:{ix[f]:c for f,c in e.items()} for U,e in cubes.items()},[{ix[f]:c for f,c in e.items()} for e in rays]


def equations(zs,ds):
    blocks=[flat(z) for z in zs];offsets=[0]
    for f,_,_ in blocks:offsets.append(offsets[-1]+len(f))
    rows=[]
    for U,o in LOCS:
        e={}
        for k,(z,d) in enumerate(zip(zs,ds)):
            active=len(U)==5 or z>>REL.index(U)&1
            if o is not None:active=active and z>>REL.index(U|{o})&1
            if active:
                for j,c in blocks[k][1].get(U,{}).items():e[offsets[k]+j]=Q(d)*c
        rows.append((e,Q(2*(-1)**(len(U)+1))))
    for q,rhs in enumerate(TARGET):
        e={}
        for k,d in enumerate(ds):
            for j,c in blocks[k][2][q].items():e[offsets[k]+j]=Q(d)*c
        rows.append((e,rhs))
    return offsets[-1],rows


def certify(zs,ds):
    m,rows=equations(zs,ds)
    for i,(e,rhs) in enumerate(rows):
        if rhs and all(c*rhs<=0 for c in e.values()):
            s=Q(1) if rhs>0 else Q(-1)
            return ["cone",[[i,str(s)]],[[j,str(-s*c)] for j,c in sorted(e.items())],[]]
    E=[(["e",i],[-rhs]+[e.get(j,Q(0)) for j in range(m)]) for i,(e,rhs) in enumerate(rows)]
    I=[(["y",i],[Q(0)]+[Q(int(i==j)) for j in range(m)]) for i in range(m)]
    feasible,proof=certified_feasible(E,I,m)
    if feasible:raise RuntimeError("No rational direct cone certificate found")
    ee=[];yy=[]
    for (typ,i),c in proof:(ee if typ=="e" else yy).append([i,c])
    return ["cone",ee,yy,[]]


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--budget",type=int,default=1200);args=ap.parse_args()
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")));signal.alarm(args.budget)
    start=time.monotonic();path=Path("overnight_fixed_natural8_proof.jsonl.gz");done=set()
    if path.exists():
        with gzip.open(path,"rt") as inp:
            for line in inp:
                r=json.loads(line);done.add((tuple(r["flats"]),tuple(r["signs"])))
    quads=json.loads(Path("overnight_fixed_natural8_coverage_quads.json").read_text());processed=0
    try:
        with (gzip.open(path,"at") if len(done)<16*len(quads) else contextlib.nullcontext(None)) as out:
            for zs in quads:
                for ds in itertools.product((1,-1),repeat=4):
                    if (tuple(zs),ds) in done:continue
                    proof=certify(zs,ds)
                    out.write(json.dumps({"flats":zs,"signs":ds,"proof":proof},separators=(",",":"))+"\n");out.flush();processed+=1
                    if processed%1000==0:print(json.dumps({"processed":processed,"seconds":time.monotonic()-start}),flush=True)
    except TimeoutError:
        print(json.dumps({"status":"BATCH_STOP","processed":processed,"seconds":time.monotonic()-start}),flush=True);return
    result={"status":"ALL_NATURAL8_K4_CONE_PROOFS_PRODUCED","cases":len(done)+processed,"seconds":time.monotonic()-start,
        "proof_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_natural8_producer.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
