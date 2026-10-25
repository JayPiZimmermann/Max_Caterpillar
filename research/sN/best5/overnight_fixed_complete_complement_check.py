"""Exact integer basis check of the sparse complement coordinate inverse."""
from itertools import combinations
from pathlib import Path
import json,hashlib

HERE=Path(__file__).resolve().parent
pairs=list(combinations(range(5),2));full=set(range(5))
def basis_ray(S):
    return [int(i in S and j not in S)for i,j in pairs]+[int(i in S)-int(4 in S)for i in range(4)]
tested=0
for j in range(14):
    a=[basis_ray(full-{i})[j]for i in range(5)]
    c=[basis_ray(full-{i,k})[j]for i,k in pairs]
    assert sum(c)==3*sum(a)
    w=[a[i]+a[k]-c[e]for e,(i,k)in enumerate(pairs)]
    linear=[-a[i]+sum(w[e]for e,(k,l)in enumerate(pairs)if l==i)for i in range(5)]
    assert sum(linear)==0
    assert w+linear[:4]==[int(i==j)for i in range(14)]
    for mask in range(32):
        T={i for i in range(5)if mask>>i&1}
        value=sum(c[e]for e,(i,k)in enumerate(pairs)if i in T and k in T)-(len(T)-2)*sum(a[i]for i in T)
        assert value==basis_ray(full-T)[j]
        tested+=1
out={'status':'PASS','basis_functions':14,'boolean_checks':tested,'inverse_coefficient_checks':196,'scope':'Exact integer identities on a basis prove the whole real comparison-span coordinate transformation. No K3 feasibility verdict.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'overnight_fixed_complete_complement_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
print(json.dumps(out,sort_keys=True))
