"""The four old-feature survivor: exact target sum and cached N9 global gate."""
from pathlib import Path
from fractions import Fraction as Q
import json,math,time
import numpy as np
from overnight_uniform_fay import HERE,KEYS,vec,target,P
from overnight_uniform_q9_full_gate import gate

COEFFICIENTS={'all;d^0;parity^0;orientation^1;deg_prod':Q(2,3),
              'all;d^0;parity^1;orientation^1;deg_prod':Q(2),
              'all;d^1;parity^0;orientation^1;one':Q(-10,3),
              'all;d^1;parity^0;orientation^1;deg_sum':Q(1)}

def value(u):
    v=vec(u);return sum(w*int(v[KEYS.index(k)])for k,w in COEFFICIENTS.items())

def target_formula(q):return Q(2**(q+2),3)*(5-3*(-1)**q-2*math.comb(2*q-2,q-2))
def mod(q):return q.numerator*pow(q.denominator,-1,P)%P

def main():
    start=time.monotonic();checks=[]
    for N in(5,7,9,11,13):
        t=target(N);s=sum(w*int(t[KEYS.index(k)])for k,w in COEFFICIENTS.items());assert s==target_formula((N-1)//2);checks.append({'arity':N,'signed_sum':str(s),'necessary_target':str(s/math.factorial(N))})
    D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());C=json.loads((HERE/'overnight_uniform_q9_quotient.json').read_text());state=json.loads((HERE/'overnight_uniform_q9_rows_state.json').read_text());scores=[mod(value(u))for u in D['units']]+[mod(target_formula(4)/math.factorial(9))];R=np.fromfile(HERE/state['matrix'],dtype='<u4').reshape(state['rows'],len(D['units'])+1);stars=[]
    for c in C['class_data']:
        deg={v:0 for v in range(1,9)}
        for a,b in c['underlying_edges']:deg[a]+=1;deg[b]+=1
        if max(deg.values())==7:stars.append(c['representative'])
    cols=[c['representative']for c in C['class_data']if c['matching']==4]+stars+[len(D['units'])];result=gate(R,cols,scores,True)
    out={'status':'FOUR_FEATURE_GLOBAL_N9_NECESSARY_GATE','coefficients':{k:str(v)for k,v in COEFFICIENTS.items()},'exact_caterpillar_checks':checks,'rows':state['rows'],'columns':len(cols),'gate':result,'scope':'Uniform local Fay compatibility follows by orientation-sign cancellation. The target formula has a direct Boolean-cube derivation. This finite modular global gate is only diagnostic; a failure requires an independently proved all-frequency relation.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
