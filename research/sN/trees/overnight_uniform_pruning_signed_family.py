"""Bounded exact N5 gate for a canonically invariant signed-root score family.

Every feature vanishes on non-perfect-matchable trees. Solving finite Fourier
relations is only a necessary test for descent, not a uniform proof.
"""
from pathlib import Path
import itertools,json,time
import networkx as nx
import sympy as S
from overnight_uniform_pruning_signed_gate import gamma
HERE=Path(__file__).parent

def score_data(u,n):
    _,md=gamma(u,n);T=nx.Graph(u['edges']);I={int(k):v for k,v in md['signed_root_counts'].items()};A=set(md['root_component']);kap={v:int(v==u['root']) for v in T}
    for v,w in u['edges']:kap[v]+=1
    from overnight_uniform_pruning_infinity import rooted_cuts
    orient=__import__('math').prod(s for _,s in rooted_cuts(u));pairs=[]
    for v in T:
        for w in T:
            d=nx.shortest_path_length(T,v,w)
            pairs.append({'weight':I[v]*I[w],'d':d,'diag':int(v==w),'inside':int(v in A)+int(w in A),'k_sum':kap[v]+kap[w],'k_prod':kap[v]*kap[w],'k_diff2':(kap[v]-kap[w])**2,'deg_sum':T.degree[v]+T.degree[w],'deg_prod':T.degree[v]*T.degree[w]})
    return orient,pairs

def features(d,mode):
    orient,pairs=d;out={}
    eligibility=['all','both','one','none']
    poly={'one':lambda p:1,'k_sum':lambda p:p['k_sum'],'k_prod':lambda p:p['k_prod'],'k_diff2':lambda p:p['k_diff2'],'deg_sum':lambda p:p['deg_sum'],'deg_prod':lambda p:p['deg_prod']}
    if mode=='basic':poly={'one':poly['one']}
    if mode=='kappa':poly={k:v for k,v in poly.items() if not k.startswith('deg')}
    for ep,pw,par,sgn,mult in itertools.product(eligibility,range(3),range(2),range(2),poly):
        val=0
        for p in pairs:
            if ep!='all' and p['inside']!={'both':2,'one':1,'none':0}[ep]:continue
            val+=p['weight']*(p['d']**pw)*((-1)**(p['d']*par))*poly[mult](p)
        if sgn:val*=orient
        out[f'{ep};d^{pw};parity^{par};orientation^{sgn};{mult}']=val
    return out

def main():
    start=time.monotonic();data=json.loads((HERE/'overnight_uniform_pruning_signed_gate.json').read_text());E=S.Matrix([[S.Rational(x) for x in r] for r in data['rows']]);A=E[:,:-1];null=S.Matrix.hstack(*A.nullspace());c,pars=A.gauss_jordan_solve(E[:,-1]);c=c.subs({p:0 for p in pars});ds=[score_data(u,5) for u in data['units']];result={'status':'EXACT_FINITE_SIGNED_FAMILY_GATE','arity':5,'modes':{}}
    for mode in('basic','kappa','degree'):
        allf=[features(d,mode) for d in ds];keys=list(allf[0]);F=S.Matrix([[f[k] for k in keys] for f in allf]);C=null.T*F;ker=C.nullspace();res={'features':len(keys),'feature_rank':F.rank(),'constraint_rank':C.rank(),'valid_score_rank':(F*S.Matrix.hstack(*ker)).rank() if ker else 0}
        for v in ker:
            response=(c.T*F*v)[0]
            if response:
                v=v/response;res['candidate']={k:str(v[i]) for i,k in enumerate(keys) if v[i]};res['assignment']=list(map(str,F*v));res['target_response']='1'
                w,wp=A.T.gauss_jordan_solve(F*v);w=w.subs({p:0 for p in wp});assert A.T*w==F*v and (w.T*E[:,-1])[0]==1
                res['evaluation_weights']=list(map(str,w));break
        result['modes'][mode]=res;print(mode,{k:v for k,v in res.items() if k not in('assignment',)},flush=True)
    result['seconds']=time.monotonic()-start;result['scope']='A saved evaluation functional certifies the assignment at N5 only. It automatically respects full rational identities at this arity. Its extension to every odd arity is unproved.'
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
