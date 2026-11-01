"""Known exact network control for the core-plus-correction MILP equations."""
import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from overnight_fixed_cross_core_mip import build


def main():
    candidate=json.loads(Path("overnight_fixed_cross_sparsify_3_2000_candidate.json").read_text());edges=candidate["first_layer_edges"]
    W=np.load("overnight_fixed_cross_dictionary_2_orientation3_candidate.npz")["forms"];indices={tuple(row):j for j,row in enumerate(W)}
    keep=list(range(1,15));core=[[indices[tuple(map(int,candidate["outer_forms"][j]))],candidate["output"][j]]for j in keep]
    auxsign=1 if Q(candidate["output"][0])>0 else -1;n,signs,A,lo,hi=build(core,edges,W,auxsign,8)
    x=list(map(Q,candidate["remainder"]))
    for j in keep+[0]:x.extend(abs(Q(candidate["output"][j]))*Q(c)for c in candidate["outer_forms"][j])
    aux=x[-7:]
    for perm in itertools.permutations(range(5)):
        values=[sum(w*int(i in perm[:k]and j not in perm[:k])for w,(i,j)in zip(aux,edges))for k in range(1,5)]
        assert min(values)>=0 or max(values)<=0
        x.append(Q(int(min(values)>=0)))
    assert len(x)==n+120 and all(abs(c)<=8 for c in x[:n])
    A=A.tocsr()
    for i in range(A.shape[0]):
        start,end=A.indptr[i:i+2]
        value=sum(Q(float(c)).limit_denominator(1000000)*x[j]for j,c in zip(A.indices[start:end],A.data[start:end]))
        if np.isfinite(lo[i]):assert value>=Q(float(lo[i]))
        if np.isfinite(hi[i]):assert value<=Q(float(hi[i]))
    result={"status":"EXACT_KNOWN_NETWORK_CORE_MIP_CONTROL_PASS","rows":A.shape[0],"variables":A.shape[1],
            "producer_sha256":hashlib.sha256(Path("overnight_fixed_cross_core_mip.py").read_bytes()).hexdigest(),
            "control_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_core_mip_control.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True))


if __name__=="__main__":main()
