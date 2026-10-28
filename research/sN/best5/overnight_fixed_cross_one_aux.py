"""Try one arbitrary correction sign-pattern beside the four-neuron core.

Patterns come from the finite dictionary, but their coefficients are then
solved over all reals. Negative verdicts concern these patterns only.
"""
import hashlib
import itertools
import json
import signal
import time
from pathlib import Path
import numpy as np
from scipy.sparse import load_npz
from overnight_fixed_cross_pattern import refine


def main():
    start=time.monotonic();A=load_npz("overnight_fixed_cross_sparse_3_matrix.npz")
    ids=np.flatnonzero(A[:-30,7:].getnnz(axis=0)==0)
    allW=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")["forms"];W=allW[ids]
    original=json.loads(Path("overnight_fixed_cross_sparsify_3_2000_candidate.json").read_text());edges=original["first_layer_edges"]
    rows=[]
    for perm in itertools.permutations(range(5)):
        V=np.asarray([[int(i in perm[:k] and j not in perm[:k]) for i,j in edges] for k in range(1,5)]).T;v=W@V
        rows.append(np.where(np.max(v,axis=1)==0,np.where(np.min(v,axis=1)==0,0,-1),1).astype(np.int8))
    patterns={}
    for j,p in enumerate(np.asarray(rows).T):patterns.setdefault(bytes(p),int(ids[j]))
    path=Path("overnight_fixed_cross_one_aux.jsonl");done=set()
    if path.exists():
        for line in path.read_text().splitlines():
            r=json.loads(line);done.add((r["form_index"],r["sign"]))
    core=[4,10,13,14];processed=0;found=False
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("declared budget")));signal.alarm(300)
    try:
        with path.open("a") as out:
            for index in patterns.values():
                for sign in(1,-1):
                    if(index,sign)in done:continue
                    candidate={"first_layer_edges":edges,"outer_forms":[original["outer_forms"][j] for j in core]+[list(map(str,allW[index]))],
                               "output":[original["output"][j] for j in core]+[str(sign)]}
                    r=refine(candidate,list(range(5)));r.update(form_index=index,sign=sign,seconds=time.monotonic()-start)
                    if "candidate" in r:
                        Path("overnight_fixed_cross_one_aux_candidate.json").write_text(json.dumps(r.pop("candidate"),indent=2)+"\n");found=True
                    out.write(json.dumps(r,separators=(",",":"))+"\n");out.flush();processed+=1
                    if processed%25==0 or found:print(json.dumps({"processed":processed,"found":found,"seconds":time.monotonic()-start}),flush=True)
                    if found:break
                if found:break
    except TimeoutError:print("DECLARED_BUDGET_REACHED",flush=True)
    finally:signal.alarm(0)
    result={"status":"EXACT_PATTERN_CANDIDATE" if found else "PATTERN_BATCH_COMPLETE","patterns":len(patterns),"processed":processed,
            "seconds":time.monotonic()-start,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_one_aux.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n");print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
