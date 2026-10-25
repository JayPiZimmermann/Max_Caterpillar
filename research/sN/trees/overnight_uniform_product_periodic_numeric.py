"""Bounded generic-frequency diagnostic for the complete binary periodization.

Finite closed formula, no lattice truncation. Double precision is a diagnostic;
N3 maximum and an independently certified N5 rational relation are controls.
"""
from pathlib import Path
from collections import Counter
import itertools,json,math,cmath,time
import numpy as np
from dfs_review_fourier import family
PI=math.pi;LAM=2j*PI

def frac(x):
    y=x-math.floor(x)
    return 0.0 if min(y,1-y)<1e-10 else y
def g(z,t):
    t=frac(t)
    if not t:return PI*cmath.cos(PI*z)/cmath.sin(PI*z)
    return PI*cmath.exp(1j*PI*(1-2*t)*z)/cmath.sin(PI*z)
def aa(z):return LAM/(1-cmath.exp(-LAM*z))

def data(U):
    n=len(U['edges'])+2;adj={i:[]for i in range(1,n)}
    for u,v in U['edges']:adj[u].append(v);adj[v].append(u)
    root=U['root'];par={root:None};order=[root]
    for v in order:
        for w in adj[v]:
            if w!=par[v]:par[w]=v;order.append(w)
    E=set(map(tuple,U['edges']));vertices=order[1:];cuts=[]
    for v in vertices:
        C={v};todo=[v]
        for w in todo:
            for x in adj[w]:
                if par.get(x)==w:C.add(x);todo.append(x)
        cuts.append(C)
    return root,par,vertices,cuts,[1 if(v,par[v])in E else -1 for v in vertices]

def one(U,p,omega,theta):
    root,par,vs,cuts,eps=data(U);N=len(p);n=N-1;z=[omega[p[v]]for v in range(N)];th=[theta[p[v]]for v in range(N)];v0=p.index(0);Q=[sum(z[v]for v in C)for C in cuts];alpha=[th[v]-th[par[v]]for v in vs]
    if v0==0:
        out=complex((-1)**(n-3))
        for q,e,t in zip(Q,eps,alpha):out*=(g(q,t)-g(q+e,t))/e
        return out
    a=z[0];beta=th[0]-th[root];inc=[j for j,v in enumerate(vs)if v==v0 or par[v]==v0]
    if len(inc)==1:
        j=inc[0];free=[k for k in range(n-1)if k!=j];be=beta-alpha[j]if root==v0 else beta;out=0j
        for bits in itertools.product((0,1),repeat=len(free)):
            coeff=complex((-1)**(n-3+sum(bits)));tau=be
            for k,d in zip(free,bits):coeff*=eps[k]*g(Q[k]+d*eps[k]*a,alpha[k]);tau-=d*eps[k]*frac(alpha[k])
            if root!=v0:H=g(a,tau)-g(a+eps[j],tau)
            elif eps[j]==1:H=g(a,tau)-g(a+1,tau)
            else:H=g(a,tau)+g(a+1,tau)-2*g(a+0.5,tau)
            out+=coeff*H
        return out
    s=[(1 if v==v0 else -1 if par[v]==v0 else 0)for v in vs];b=int(root==v0);out=0j
    for delta in itertools.product((0,1),repeat=n-1):
        ap=[aa(q+d*e*a)for q,d,e in zip(Q,delta,eps)];pre=complex((-1)**(n-3+sum(delta))*math.prod(eps))*LAM*aa(a)*math.prod(ap)
        c=-b-sum(d*e*ss for d,e,ss in zip(delta,eps,s))
        for left,right in((0.0,0.5),(0.5,1.0)):
            mid=(left+right)/2;off=[frac(t+ss*mid)-ss*mid for t,ss in zip(alpha,s)];gamma0=beta-sum(d*e*f for d,e,f in zip(delta,eps,off));points=[left,right]
            if c:
                lo=min(gamma0+c*left,gamma0+c*right);hi=max(gamma0+c*left,gamma0+c*right)
                for k in range(math.floor(lo)-1,math.ceil(hi)+2):
                    t=(k-gamma0)/c
                    if left+1e-10<t<right-1e-10:points.append(t)
            points=sorted(set(points))
            for x,y in zip(points,points[1:]):
                k=math.floor(gamma0+c*(x+y)/2+1e-10);C=pre*cmath.exp(-LAM*(sum(f*q for f,q in zip(off,Q))+(beta-k)*a));L=gamma0-k+1/(cmath.exp(LAM*a)-1)
                primitive=lambda t:-cmath.exp(-LAM*t)*((L+c*t)/LAM+c/LAM**2)
                out+=C*(primitive(y)-primitive(x))
    return out

def permutations(U):
    N=len(U['edges'])+2;seen={}
    for p in itertools.permutations(range(N)):
        h=[0]*N;h[p[U['root']]]+=1;h[p[0]]-=1;E=[]
        for u,v in U['edges']:
            u,v=p[u],p[v];E.append(tuple(sorted((u,v))))
            if u>v:h[u]+=1;h[v]-=1
        key=(tuple(h),tuple(sorted(E)))
        if key in seen:seen[key][1]+=1
        else:seen[key]=[p,1]
    return list(seen.values())
def full(U,omega,theta):return sum(mult*one(U,p,omega,theta)for p,mult in permutations(U))
def maximum(omega,theta):
    z=omega[1:];B=sum(w for w,t in zip(omega,theta)if t==0.5)
    return -2*PI**(len(z)-1)*cmath.sin(PI*B)/math.prod(cmath.sin(PI*w)for w in z)

def main():
    start=time.monotonic();u3={'root':1,'edges':[(2,1)]};o3=[1,0.17j,-1-0.17j];th3=[0,0,0.5];got3=full(u3,o3,th3);want3=6*maximum(o3,th3);assert abs(got3-want3)<1e-9*max(1,abs(want3));print('N3 control',abs(got3-want3),flush=True)
    star={'root':1,'edges':[(2,1),(3,2),(4,2)]};path={'root':1,'edges':[(2,1),(1,3),(2,4)]};units=family(5,'nopath');theta=[0,0.5,0.5,0,0];triples=list(itertools.combinations([2,3,5,7,11,13],3))[:14];rows=[];controls=[]
    for triple in triples:
        z=[1j*math.log(x)/(2*PI)for x in triple];omega=[1]+z+[-1-sum(z)];row=[full(U,omega,theta)for U in units];target=maximum(omega,theta);control=abs(full(star,omega,theta)-3*full(path,omega,theta))/max(1,abs(target));controls.append(control);assert control<1e-7;scale=max(abs(v)for v in row+[target]);rows.append([v/scale for v in row+[target]]);print('row',triple,'control',control,'elapsed',time.monotonic()-start,flush=True)
    R=np.array(rows,dtype=complex);sv=np.linalg.svd(R[:,:-1],compute_uv=False);sa=np.linalg.svd(R,compute_uv=False);out={'status':'MEASURED_COMPLETE_PERIODIZATION_GATE','precision':'complex128','points':triples,'rows':[[[v.real,v.imag]for v in row]for row in rows],'ordinary_singular_values':sv.tolist(),'augmented_singular_values':sa.tolist(),'maximum_control_error':max(controls),'scope':'Closed finite formula includes every apex placement. Floating-point rank is diagnostic only. Exact N3 and N5 identities supply numerical controls, not a full independent symbolic validation.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('sv',sv,'aug',sa,'seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
