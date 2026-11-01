"""All-width span test using every exact natural8 vanishing flat.

On a fixed flat, distinct nonproportional absolute linear forms are
linearly independent as functions of the flat parameters. Thus their
coefficient columns span all possible one-neuron locality/ray vectors.
A left-kernel separator from all such columns would rule out every
finite second width. A successful target span is only a failed necessary
test, not a construction.
"""
import hashlib
import json
import time
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_natural8_k4 import FLATS,SETS,REL,ANN,TARGET,data
from flats_loc import nullspace


def main():
    start=time.monotonic();columns=[];locations=[]
    locality=[(U,o) for U in REL if len(U)==3 for o in range(5) if o not in U]
    locality += [(U,None) for U in SETS if len(U) in (4,5)]
    for z in sorted(FLATS):
        _,cubes,rays=data(z);rows=[]
        for U,o in locality:
            active=len(U)==5 or z>>REL.index(U)&1
            if o is not None:active=active and z>>REL.index(U|{o})&1
            rows.append(cubes.get(U,{}) if active else {})
        rows+=rays;forms=sorted({f for e in rows for f in e})
        for f in forms:
            columns.append([e.get(f,Q(0)) for e in rows]);locations.append([z,list(map(str,f))])
    target=[Q(2*(-1)**(len(U)+1)) for U,o in locality]+TARGET
    annihilator=nullspace(columns,len(target));separators=[a for a in annihilator if sum(x*y for x,y in zip(a,target))]
    result={"status":"ALL_WIDTH_NECESSARY_SEPARATOR_FOUND" if separators else "TARGET_IN_ALL_WIDTH_NECESSARY_SPAN",
        "flats":len(FLATS),"columns":len(columns),"equations":len(target),"rank":len(target)-len(annihilator),
        "annihilator_dimension":len(annihilator),"separator_count":len(separators),
        "separators":[list(map(str,a)) for a in separators],"seconds":time.monotonic()-start,
        "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope":"Necessary locality/ray span; a separator requires independent coverage/checking and the mathematical bridge"}
    Path("overnight_fixed_natural8_allwidth.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
