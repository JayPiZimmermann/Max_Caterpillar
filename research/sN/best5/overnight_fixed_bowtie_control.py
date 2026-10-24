"""Exact positive control for the independent K3 equation checker.

Substitute the four free neurons of the already certified (10,6)
network directly into all 48 independently rebuilt necessary equations.
"""
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
import overnight_fixed_bowtie_verify as verifier


def main():
    verifier.initialize()
    net=json.loads(Path("netB_10_6.json").read_text())
    W=[[Q(c) for c in row] for row in net["second_layer"]]
    d=[Q(c) for c in net["output"]]
    zs=[];ds=[];coords=[]
    for k in range(2,6):
        assert W[k][8:]==[0,0]
        w=[abs(d[k])*c for c in W[k][:8]]
        z=sum(1<<i for i,S in enumerate(verifier.REL) if sum(a*b for a,b in zip(w,verifier.VALUE[S]))==0)
        B=verifier.BASES[z];local=[]
        for j,row in enumerate(B):
            col=next(p for p in range(8) if row[p]==1 and all(i==j or bb[p]==0 for i,bb in enumerate(B)))
            local.append(w[col])
        assert all(sum(local[j]*B[j][i] for j in range(len(B)))==w[i] for i in range(8))
        zs.append(z);ds.append(1 if d[k]>0 else -1);coords.extend(local)
    equation,forms,_=verifier.case_data(zs,ds)
    values=[abs(sum(a*b for a,b in zip(f,coords))) for f in forms]
    for i in range(48):
        e,rhs=equation(i);assert sum(c*values[j] for j,c in e.items())==rhs
    result={"status":"INDEPENDENT_48_EQUATION_K4_POSITIVE_CONTROL_PASS","equations":48,
            "network_sha256":hashlib.sha256(Path("netB_10_6.json").read_bytes()).hexdigest(),
            "checker_sha256":hashlib.sha256(Path("overnight_fixed_bowtie_verify.py").read_bytes()).hexdigest(),
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_bowtie_control.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
