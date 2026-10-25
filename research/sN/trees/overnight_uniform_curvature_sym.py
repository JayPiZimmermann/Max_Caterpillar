"""Bounded full-label star controls for the normalized crease operator."""
from pathlib import Path
from collections import Counter
import itertools,json,time
from fractions import Fraction as Q
from overnight_uniform_curvature import unit_score,HERE,volume

def main():
    start=time.monotonic();U={'root':1,'edges':[(2,1),(3,1),(4,1)]};counter=Counter()
    for p in itertools.permutations(range(5)):
        counter[(p[0],p[U['root']],tuple(sorted((p[u],p[v])for u,v in U['edges'])))]+=1
    rows=[];total=Q(0);negative=Q(0)
    for(apex,root,E),weight in counter.items():
        value,parts=unit_score({'apex':apex,'root':root,'edges':E});nv,np=unit_score({'apex':apex,'root':root,'edges':E,'input_sign':-1});total+=weight*value;negative+=weight*nv;rows.append({'apex':apex,'root':root,'edges':E,'multiplicity':weight,'score':str(value),'corner_scores':list(map(str,parts)),'negative_input_score':str(nv),'negative_input_corner_scores':list(map(str,np))})
    assert total==6 and negative==-39
    out={'status':'EXACT_FULL_SYMMETRIC_INWARD_STAR_CURVATURE_CONTROL','original_unit':U,'distinct_relabelings':len(counter),'total_multiplicity':sum(counter.values()),'unaveraged_full_S5_score':str(total),'negative_input_full_S5_score':str(negative),'oddized_full_S5_score':str(total-negative),'maximum_full_S5_score':120,'oddized_maximum_full_S5_score':240,'rows':rows,'scope':'Exact rational hyperplane-section volume computation. Both symmetrized and oddized operators fail to annihilate this canonical star. This does not refute a relative or tensor-valued curvature construction.','seconds':time.monotonic()-start,'volume_cache':str(volume.cache_info())};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='rows'},indent=2),flush=True)

if __name__=='__main__':main()
