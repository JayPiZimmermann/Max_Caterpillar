"""Three-free-neuron construction search with one prescribed preactivation shape.

For output signs (+,+,-), on each braid cone every interior hyperplane
must cancel. Once the first preactivation is fixed up to positive scale,
all cancellation possibilities are finite linear cases. Bounds are only
for candidate discovery; no negative theorem is claimed.
"""
import argparse,hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
from overnight_fixed_fullpair_dictionary import SETS,FEATURE,CHAINS,MOBIUS,primitive
from overnight_fixed_fullpair_pattern import network
from overnight_fixed_cross_verify import check


def build(g,target,B,quadzero=False,fixed=None):
    g=np.asarray(g,dtype=int);nv=149;rows=[];lo=[];hi=[];lower=[0]+[-np.inf]*28+[0]*60+[0]*60;upper=[B/max(abs(g))]+[np.inf]*28+[B]*60+[1]*60;integer=[0]*89+[1]*60;h0=1;k0=15;uh=29;uk=59;zh=89;zk=119
    def allocate(low,up,integ=0):
        nonlocal nv
        i=nv;nv+=1;lower.append(low);upper.append(up);integer.append(integ);return i
    def add(row,l,h):rows.append({i:float(c)for i,c in row.items()if c});lo.append(float(l));hi.append(float(h))
    def combine(*terms):
        result={}
        for term in terms:
            for i,c in term.items():result[i]=result.get(i,0)+c
        return result
    def value(start,s,scale=1):return {start+i:scale*int(v)for i,v in enumerate(FEATURE[s])if v}
    def conditional(row,y,M,kind='eq'):
        if kind=='eq':add(combine(row,{y:M}),-np.inf,M);add(combine(row,{y:-M}),-M,np.inf)
        elif kind=='ge':add(combine(row,{y:-M}),-M,np.inf)
        else:raise ValueError(kind)
    for start,u,z in((h0,uh,zh),(k0,uk,zk)):
        for s in range(30):
            v=value(start,s);add(v,-B,B);add(combine({u+s:1},{i:-c for i,c in v.items()}),0,np.inf);add(combine({u+s:1,z+s:B},{i:-c for i,c in v.items()}),-np.inf,B);add({u+s:1,z+s:-B},-np.inf,0)
            if quadzero and SETS[s].bit_count()==4:add(v,0,0)
    for q,m in enumerate(MOBIUS):
        row={0:sum(int(c)*max(int(v),0)for c,v in zip(m,g))}
        for s,c in enumerate(m):
            if c:row[uh+s]=int(c);row[uk+s]=-int(c)
        add(row,int(target[q]),int(target[q]))
    for ch in CHAINS:
        vals=g[ch];mixed=min(vals)<0<max(vals);choices=[]
        if mixed:
            # Positive second preactivation has fixed sign; the negative one
            # cancels the prescribed first form exactly, with either orientation.
            for sh,sk in itertools.product((1,-1),repeat=2):
                y=allocate(0,1,1);choices.append(y)
                for s in ch:
                    conditional(value(h0,s,sh),y,B,'ge');conditional(combine(value(k0,s),{0:-sk*int(g[s])}),y,2*B)
            # All crossing forms are proportional to the prescribed shape.
            eta=allocate(-B,B);zeta=allocate(-B,B)
            for sh,sk in itertools.product((1,-1),repeat=2):
                y=allocate(0,1,1);choices.append(y)
                conditional({eta:sh},y,B,'ge');conditional({zeta:sk},y,B,'ge');conditional({zeta:sk,0:-1,eta:-sh},y,3*B)
                for s in ch:
                    conditional(combine(value(h0,s),{eta:-int(g[s])}),y,B*(1+abs(int(g[s]))));conditional(combine(value(k0,s),{zeta:-int(g[s])}),y,B*(1+abs(int(g[s]))))
        else:
            for sh,sk in itertools.product((1,-1),repeat=2):
                y=allocate(0,1,1);choices.append(y)
                for s in ch:conditional(value(h0,s,sh),y,B,'ge');conditional(value(k0,s,sk),y,B,'ge')
            for orientation in(1,-1):
                y=allocate(0,1,1);choices.append(y)
                for s in ch:conditional(combine(value(h0,s),value(k0,s,-orientation)),y,2*B)
        add({y:1 for y in choices},1,1)
    if fixed is not None:
        alpha,h,k=fixed
        for j,v in enumerate([alpha]+list(h)+list(k)):lower[j]=upper[j]=float(v)
    rr=[];cc=[];vv=[]
    for r,row in enumerate(rows):
        for c,v in row.items():rr.append(r);cc.append(c);vv.append(v)
    A=coo_matrix((vv,(rr,cc)),shape=(len(rows),nv)).tocsc()
    return A,np.asarray(lo),np.asarray(hi),np.asarray(integer),np.asarray(lower),np.asarray(upper)


def solve(g,target,B,budget,quadzero=False,fixed=None):
    A,lo,hi,integer,lb,ub=build(g,target,B,quadzero,fixed);r=milp(c=np.zeros(A.shape[1]),integrality=integer,bounds=Bounds(lb,ub),constraints=LinearConstraint(A,lo,hi),options={'time_limit':budget,'disp':False});return r,A,lo,hi


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--budget',type=int,default=180);ap.add_argument('--bound',type=int,default=8);ap.add_argument('--quadzero',action='store_true');args=ap.parse_args();start=time.monotonic();prefix=f'overnight_fixed_fullpair_fixedshape_{int(args.quadzero)}';FF=sp.Matrix(FEATURE.tolist())
    # Positive control: a nontrivial three-form cancellation core from the
    # exact dictionary, with its own globally braid-linear target.
    source='overnight_fixed_fullpair_dictionary_1';V=np.load(source+'_values.npz')['values'];core=json.loads(Path(source+'_cores.json').read_text())['records'][0];ids=core['indices'];weights=list(map(Q,core['weights']));pos=[j for j,d in enumerate(weights)if d>0];neg=[j for j,d in enumerate(weights)if d<0];assert len(pos)==2 and len(neg)==1
    p,q=pos;r=neg[0];g=V[ids[p]];alpha=weights[p];h=np.asarray([weights[q]*int(x)for x in V[ids[q]]],dtype=object);k=np.asarray([-weights[r]*int(x)for x in V[ids[r]]],dtype=object);target=MOBIUS@np.asarray([alpha*max(int(a),0)+max(b,0)-max(c,0)for a,b,c in zip(g,h,k)],dtype=object);hp=[Q(x)for x in FF.gauss_jordan_solve(sp.Matrix(h.tolist()))[0]];kp=[Q(x)for x in FF.gauss_jordan_solve(sp.Matrix(k.tolist()))[0]]
    # Scale the rational control to make its target integral as required by the builder.
    den=math.lcm(*(Q(x).denominator for x in target),alpha.denominator,*(Q(x).denominator for x in hp+kp));alpha*=den;hp=[x*den for x in hp];kp=[x*den for x in kp];target=np.asarray([int(x*den)for x in target]);control,A,lo,hi=solve(g,target,max(8,args.bound*den),20,fixed=(alpha,hp,kp));assert control.x is not None,control.message
    x=[Q(float(c)).limit_denominator(1000000)for c in control.x];values=A@np.asarray([float(c)for c in x]);assert max(np.maximum(lo-values,values-hi))<1e-9
    control_receipt={'status':'FIXED_NONTRIVIAL_THREE_CORE_CONTROL_PASS','solver_status':control.status,'variables':A.shape[1],'constraints':A.shape[0]};print(json.dumps(control_receipt),flush=True)
    known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());w=list(map(Q,known['second_layer'][2][:14]));gg=[sum(c*int(f)for c,f in zip(w,row))for row in FEATURE];den=math.lcm(*(c.denominator for c in gg));g=np.asarray(primitive([int(c*den)for c in gg]));target=np.asarray([(-1)**(s.bit_count()+1)for s in range(32)if s.bit_count()>=3]);result,A,lo,hi=solve(g,target,args.bound,args.budget,args.quadzero);report={'status':'FIXED_SHAPE_CONSTRUCTION_SEARCH_INCOMPLETE','quadruple_values_zero':args.quadzero,'bound':args.bound,'solver_status':result.status,'message':result.message,'variables':A.shape[1],'constraints':A.shape[0],'seconds':time.monotonic()-start,'positive_control':control_receipt,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if result.x is not None:
        x=[Q(float(c)).limit_denominator(1000000)for c in result.x];gw=[Q(c)*x[0]for c in FF.gauss_jordan_solve(sp.Matrix(g.tolist()))[0]];WW=[gw,x[1:15],x[15:29]];DD=[1,1,-1];targetvalues=[Q(1-int(s&1))-sum(d*max(sum(w*int(f)for w,f in zip(row,FEATURE[q])),Q(0))for d,row in zip(DD,WW))for q,s in enumerate(SETS)];R=[Q(c)for c in FF.gauss_jordan_solve(sp.Matrix(targetvalues))[0]];cand={'remainder':list(map(str,R)),'outer_forms':[list(map(str,row))for row in WW],'output':list(map(str,DD))};path=Path(prefix+'_net.json');path.write_text(json.dumps(network(cand),indent=2)+'\n');receipt=check(path);Path(prefix+'_check.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');report['status']='EXACT_MATCHED_SIXTEEN_FIVE_CONSTRUCTION'
    Path(prefix+'.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()
