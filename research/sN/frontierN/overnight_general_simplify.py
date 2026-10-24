"""Bounded diagnostic: how few lexicographic flag kinds force the same exclusion?

Reuses the producer for exploration only; does not replace its independent check.
"""
from itertools import product, permutations
from pathlib import Path
import json, time
from overnight_general_flags import FAMILIES, components, contradiction

def run():
    start=time.monotonic(); records=[]
    for mode in ['positive','negative','same_sign','one_positive','one_negative']:
        if mode=='positive': epss=[(1,)*5]
        elif mode=='negative': epss=[(-1,)*5]
        elif mode=='same_sign': epss=[(-1,)*5,(1,)*5]
        elif mode=='one_positive': epss=[(-1,)*5]+[tuple(1 if i==j else -1 for i in range(5)) for j in range(5)]
        else: epss=[(1,)*5]+[tuple(-1 if i==j else 1 for i in range(5)) for j in range(5)]
        flags=list(product(permutations(range(5)),epss)); counts=[]
        for fam in FAMILIES:
            choices=[[s for s in product((-1,1),repeat=len(sup)) if len(set(s))==2] for sup in fam]
            excluded=0; survivors=[]
            for signs in product(*choices):
                seen={}; comps={}
                for perm,eps in flags:
                    priority={v:k for k,v in enumerate(perm)}
                    active=tuple(j for j,sup in enumerate(fam)
                        if signs[j][sup.index(max(sup,key=priority.get))]*eps[max(sup,key=priority.get)]>0)
                    winner=max(range(5),key=lambda i:eps[i]*2**priority[i])
                    if active not in comps: comps[active]=components(fam,active)
                    for c in comps[active]:
                        mask=sum(1<<i for i in c); rhs=int(winner in c)
                        seen.setdefault((mask,rhs),(perm,eps,active,winner,c))
                cs=[(mask,rhs,w) for (mask,rhs),w in sorted(seen.items())]
                if contradiction(cs): excluded+=1
                else: survivors.append(signs)
            counts.append({'excluded':excluded,'survivors':survivors})
        record={'mode':mode,'flag_count':len(flags),'results':counts}; records.append(record)
        print(mode,len(flags),[(c['excluded'],len(c['survivors'])) for c in counts],flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps({'seconds':time.monotonic()-start,'results':records},indent=2)+'\n')

if __name__=='__main__':run()
