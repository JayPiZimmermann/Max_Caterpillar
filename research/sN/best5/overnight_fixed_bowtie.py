"""Exact vanishing-flat inventory for the certified 10-row first layer.

The eight translation-invariant features form two triangles sharing the
coordinate x1. All real combinations are allowed, including boundaries.
This inventory only gives necessary locality conditions; it is not a
network-width certificate by itself.
"""
import itertools
import json
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

from flats_loc import nullspace, REL
from overnight_fixed_k2 import canonical

N=5
NET=json.loads(Path("netB_10_6.json").read_text())
A=[[Q(c) for c in row] for row in NET["first_layer"][:8]]
ALL=[frozenset(c) for r in range(1,6) for c in itertools.combinations(range(5),r)]
VR={S:tuple(max(sum(a[i] for i in S),0) for a in A) for S in ALL}
LOCS=[(T,o) for T in REL if len(T)==3 for o in range(5) if o not in T]


def inventory():
    unique=sorted(set(r for S,r in VR.items() if S in REL and any(r)))
    seen={}
    for mask in range(1<<len(unique)):
        basis=nullspace([r for j,r in enumerate(unique) if mask>>j&1],8)
        if not basis:
            continue
        forms={S:tuple(sum(a*b for a,b in zip(row,v)) for v in basis) for S,row in VR.items()}
        Z=sum(1<<j for j,S in enumerate(REL) if not any(forms[S]))
        if Z in seen:
            continue
        qm={}
        for U in REL:
            if any(forms[U]):
                continue
            expr={}
            for W in ALL:
                if not W<U:
                    continue
                f,c=canonical(forms[W])
                if f is not None:
                    expr[f]=expr.get(f,Q(0))+c*(-1)**(len(U)-len(W))
            qm[U]={f:c for f,c in expr.items() if c}
        cover=0
        for q,(T,o) in enumerate(LOCS):
            if not any(forms[T]) and not any(forms[T|{o}]) and qm[T]:
                cover|=1<<q
        # A needed 4-tie is likewise covered only when its entire
        # absolute-value expression is not identically zero.
        for j,U in enumerate(S for S in REL if len(S)==4):
            if not any(forms[U]) and qm[U]:
                cover|=1<<(20+j)
        seen[Z]={"dimension":len(basis),"cover":cover,
                 "basis":[[str(c) for c in b] for b in basis]}
    return unique,seen


if __name__=="__main__":
    t=time.monotonic()
    unique,flats=inventory()
    masks=sorted(set(row["cover"] for row in flats.values()))
    full=(1<<25)-1
    pairs=[(a,b) for i,a in enumerate(masks) for b in masks[i:] if a|b==full]
    triple_masks=[]
    for i,a in enumerate(masks):
        for j in range(i,len(masks)):
            b=masks[j]
            missing=full^(a|b)
            for c in masks[j:]:
                if c&missing==missing:
                    triple_masks.append((a,b,c))
    counts=Counter(row["cover"] for row in flats.values())
    triple_upper=sum(counts[a]*counts[b]*counts[c] for a,b,c in triple_masks)
    result={"status":"EXACT_NECESSARY_COVER_INVENTORY","unique_hyperplanes":len(unique),
            "flats":flats,"dimension_counts":dict(Counter(row["dimension"] for row in flats.values())),
            "coverage_masks":len(masks),"covering_mask_pairs":len(pairs),
            "covering_mask_triples":len(triple_masks),"flat_triples_upper":triple_upper,
            "triple_masks":triple_masks,"seconds":time.monotonic()-t}
    Path("overnight_fixed_bowtie_inventory.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ("flats","triple_masks")},sort_keys=True),flush=True)
