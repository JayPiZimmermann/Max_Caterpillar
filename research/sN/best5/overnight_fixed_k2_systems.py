"""Export the proposed linear systems separately from the proof trees.

The independent checker verifies every exported system against unreduced
cube equations, so this exporter is outside the trusted arithmetic core.
"""
import gzip
import itertools
import json
import pickle
from pathlib import Path
from k2_exact import F
from overnight_fixed_k2 import equations


def main():
    work=pickle.loads(Path("k2_work.pkl").read_bytes())
    bases={}
    with gzip.open("overnight_fixed_k2_systems.jsonl.gz","wt") as out:
        for idx,zs in enumerate(work):
            for z in zs:
                bases[str(z)]=[[str(x) for x in row] for row in F[z][1]]
            for ds in itertools.product((1,-1),repeat=2):
                problem=equations(list(zs),ds)
                if problem is None:
                    data=None
                else:
                    n,offsets,rows=problem
                    forms=sorted({f for e,r in rows for f in e})
                    ids={f:i for i,f in enumerate(forms)}
                    data={"n":n,"offsets":offsets,"forms":[[str(x) for x in f] for f in forms],
                          "rows":[[[[ids[f],str(c)] for f,c in e.items()],str(r)] for e,r in rows]}
                out.write(json.dumps({"case":idx,"flats":zs,"signs":ds,"system":data},separators=(",",":"))+"\n")
    Path("overnight_fixed_k2_bases.json").write_text(json.dumps(bases,sort_keys=True,separators=(",",":"))+"\n")
    print(json.dumps({"status":"EXPORTED","pairs":len(work),"bases":len(bases)}),flush=True)


if __name__=="__main__":main()
