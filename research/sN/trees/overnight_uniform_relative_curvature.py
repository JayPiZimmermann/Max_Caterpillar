"""Independent exact all-chart obstruction using only cone dominance.

No volumes, Fourier evaluations, linear algebra, or research producers.
"""
from pathlib import Path
import itertools,json,time

def subtract(a,b):return tuple(x-y for x,y in zip(a,b))
def gap_coeff(v):a,b,d,e=v;return(a,a+b,d,d+e)
def dominates(a,b):return all(x>=0 for x in gap_coeff(subtract(a,b)))
def crease(v):
    a,b,d,e=v
    if b+e or not b:return 0
    relu=lambda x:max(x,0)
    return relu(a+b)-relu(a)-relu(d)+relu(d-b)

def corner_extreme(subset,bits,maximum):
    X=[(0,0,0,0),(1,0,0,0)if not bits[0]else(-1,1,0,0),(0,1,0,0),(0,0,1,0)if not bits[1]else(0,0,-1,1),(0,0,0,1)]
    candidates=[X[i]for i in subset]
    active=[v for v in candidates if not any(w!=v and(dominates(w,v)if maximum else dominates(v,w))for w in candidates)]
    assert len(active)<=2
    if len(active)<2:return 0
    return(1 if maximum else-1)*crease(subtract(*active))

def score(subset,maximum):
    return sum((-1)**sum(bits)*corner_extreme(subset,bits,maximum)for bits in itertools.product((0,1),repeat=2))

def main():
    start=time.monotonic();all_labels=set(range(5));fullmax=score(all_labels,True);fullmin=score(all_labels,False);assert fullmax==fullmin==1;rows=[]
    for omitted in range(5):
        labels=all_labels-{omitted};a=score(labels,True);b=score(labels,False)
        assert a==int(omitted==0)and b==int(omitted in(2,4))
        rows.append({'omitted_label':omitted,'max_score':a,'min_score':b,'reflected_max_score':-b,'reflected_min_score':-a})
    assert 3*fullmax==sum(r['max_score']+r['min_score']for r in rows)
    assert -3*fullmin==sum(r['reflected_max_score']+r['reflected_min_score']for r in rows)
    out={'status':'EXACT_ALL_SCALAR_CHARTS_TOP_QUOTIENT_NO_GO','full_maximum_score':fullmax,'full_minimum_score':fullmin,'facets':rows,'identity_annihilated_by_every_chart':'max5-(1/3)*sum_j(max_without_j+min_without_j)','scope':'Relabeling gives every reference apex, pairing, and block ordering. The table also covers input reflection. Every scalar linear combination of these operators that annihilates L3 must annihilate max5. This does not exclude flag operators or a tensor carrying new overlap data.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
