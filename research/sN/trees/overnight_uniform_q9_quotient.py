"""Exact whole-function quotient by tree automorphisms and invariant kappa.

U=sigma(sum_v kappa_v*x_v-sum_edges min(x_u,x_v)-x_apex), so these
identifications are analytic equalities, independent of sampled rows.
"""
from pathlib import Path
from collections import defaultdict
import json,time
import networkx as nx
import numpy as np
from overnight_uniform_q9_shapes import shape
HERE=Path(__file__).parent;BASE=Path(__file__).with_suffix('')

def main():
    start=time.monotonic();D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());groups=defaultdict(list)
    for j,U in enumerate(D['units']):groups[shape(U)].append(j)
    reps=[];mapping=[None]*len(D['units']);classdata=[];bad=0
    for E,js in groups.items():
        G=nx.Graph(E);nodes=sorted(G);autos=list(nx.algorithms.isomorphism.GraphMatcher(G,G).isomorphisms_iter());matching=len(nx.max_weight_matching(G,maxcardinality=True));seen={}
        for j in js:
            U=D['units'][j];k={v:int(v==U['root'])for v in nodes}
            for u,v in U['edges']:k[u]+=1
            key=min(tuple(k[a[v]]for v in nodes)for a in autos)
            if key not in seen:
                seen[key]=len(reps);reps.append(j);classdata.append({'representative':j,'underlying_edges':E,'kappa_key':key,'matching':matching});bad+=int(matching<4)
            c=seen[key];mapping[j]=c;assert D['scores'][j]==D['scores'][reps[c]]
    R=np.fromfile(HERE/'overnight_uniform_q9_rows576.u32',dtype='<u4').reshape(576,len(D['units'])+1)
    for j,c in enumerate(mapping):assert np.array_equal(R[:,j],R[:,reps[c]])
    assert bad==3822
    out={'status':'EXACT_KAPPA_WHOLE_FUNCTION_QUOTIENT','raw_columns':len(D['units']),'classes':len(reps),'deficient_classes':bad,'perfectly_matchable_classes':len(reps)-bad,'representatives':reps,'column_to_class':mapping,'class_data':classdata,'Q_score_constant_on_each_class':True,'independent_576_row_arithmetic_control':True,'scope':'Equality follows from the displayed min-function identity and graph relabeling. This map does not use sampled proportionalities between different kappa classes.','seconds':time.monotonic()-start};BASE.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k not in('representatives','column_to_class','class_data')},flush=True)
if __name__=='__main__':main()
