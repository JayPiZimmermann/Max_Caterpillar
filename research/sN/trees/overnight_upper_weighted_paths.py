#!/usr/bin/env python3
"""Full-symmetric weighted-path controls for a genuine cyclic enlargement.

The path signature records (head sum, positive edge magnitude) at successive
suffix cuts. A shared subset DAG sums every label permutation exactly.
Only modular span diagnostics are claimed by the probe command.
"""
from fractions import Fraction as Q
from itertools import permutations,product
from pathlib import Path
import hashlib,json,math,random,struct,subprocess,sys,time
import numpy as np
from flint import nmod_mat,ctx

HERE=Path(__file__).parent
P=1000000007
ctx.threads=1


def canonical(signature):
    signature=tuple(signature)
    return min(signature,tuple((1-h-w,w) for h,w in signature[::-1]))


def family(n,mode):
    m=n-1;out=set()
    patterns=[([1]*(m-1),range(-2,3) if mode=='shift2' else (-1,0,1))]
    if mode=='weighted2':
        patterns=[([1]*(m-1),range(-2,3))]
        for j in range(m-1):
            weights=[1]*(m-1);weights[j]=2;patterns.append((weights,(-1,0,1)))
    for weights,shifts in patterns:
        for root,shift,mask in product(range(m),shifts,range(1<<(m-1))):
            signature=[(int(root>=i)-shift-(weights[i-1] if mask>>(i-1)&1 else 0),weights[i-1]) for i in range(1,m)]
            out.add(canonical(signature))
    return sorted(out)


class Compiler:
    def __init__(self,n):
        self.n=n;self.starts=[0];self.left=[];self.factors=[];self.state={};self.factor_keys=[];self.factor_index={}
    def function(self,signature,mask):
        assert mask.bit_count()==len(signature)+1
        if not signature:return 0
        key=(signature,mask)
        if key not in self.state:
            h,w=signature[0];terms=[]
            for i in range(self.n-1):
                if not mask>>i&1:continue
                subset=mask^(1<<i);child=self.function(signature[1:],subset);factor=(subset,h,w)
                if factor not in self.factor_index:self.factor_index[factor]=len(self.factor_keys);self.factor_keys.append(factor)
                terms.append((child,self.factor_index[factor]))
            for child,factor in terms:self.left.append(child);self.factors.append(factor)
            self.starts.append(len(self.left));self.state[key]=len(self.starts)-1
        return self.state[key]
    def compile(self,signatures):self.roots=[self.function(tuple(s),(1<<(self.n-1))-1) for s in signatures];return self
    def save(self,path):
        with path.open('wb') as f:
            f.write(struct.pack('<6Q',0x5557504154483031,self.n,len(self.starts)-1,len(self.left),len(self.roots),len(self.factor_keys)))
            for array,dtype in [(self.starts,'<u4'),(self.left,'<u4'),(self.factors,'<u4'),(self.roots,'<u4'),
                                ([s for s,h,w in self.factor_keys],'<u4'),([h for s,h,w in self.factor_keys],'<i4'),([w for s,h,w in self.factor_keys],'<u4')]:
                np.asarray(array,dtype=dtype).tofile(f)
    def evaluate(self,point,prime=None):
        result=[0]*len(self.roots)
        for apex,a in enumerate(point):
            frequencies=[x for i,x in enumerate(point) if i!=apex];sums=[0]*(1<<(self.n-1))
            for mask in range(1,len(sums)):
                bit=mask&-mask;sums[mask]=sums[mask^bit]+frequencies[bit.bit_length()-1]
            fs=[]
            for mask,h,w in self.factor_keys:
                den=(sums[mask]+a*h)*(sums[mask]+a*(h+w))
                fs.append(w*pow(den%prime,-1,prime)%prime if prime else Q(w,den))
            values=[1]+[0]*(len(self.starts)-1)
            for state in range(1,len(values)):
                value=sum(values[self.left[j]]*fs[self.factors[j]] for j in range(self.starts[state-1],self.starts[state]))
                values[state]=value%prime if prime else value
            for j,r in enumerate(self.roots):result[j]+=(-a)**(self.n-4)*values[r];result[j]=result[j]%prime if prime else result[j]
        return result


def value(signature,point):
    a=point[0];frequencies=point[1:];result=Q((-a)**(len(point)-4))
    for i,(h,w) in enumerate(signature,1):
        q=sum(frequencies[i:]);result*=Q(w,(q+a*h)*(q+a*(h+w)))
    return result


def chamber(signature,point):
    n=len(point);m=n-1;head=[-1]+[0]*m;head[1]=1-signature[0][0]
    for i in range(1,m):head[i+1]=signature[i-1][0]-(signature[i][0] if i<m-1 else 0)
    result=Q(0)
    for pi in permutations(range(n)):
        pos={v:j for j,v in enumerate(pi)};slope=head.copy()
        for i,(h,w) in enumerate(signature,1):
            if pos[i+1]<pos[i]:slope[i+1]+=w;slope[i]-=w
        aa=oo=0;A=[];O=[]
        for v in pi[:-1]:aa+=slope[v];oo+=point[v];A.append(aa);O.append(oo)
        for j in range(n-1):
            if A[j]<=0:continue
            den=O[j]**2
            for k in range(n-1):
                if j!=k:den*=A[j]*O[k]-A[k]*O[j]
            result+=Q(A[j]**(n-1),den)
    return result


def controls():
    rng=random.Random(25102591);records=[]
    for n in (4,5):
        signatures=rng.sample(family(n,'weighted2'),6);dag=Compiler(n).compile(signatures)
        for attempt in range(100):
            point=[rng.randrange(1,500) for _ in range(n-1)];point.insert(0,-sum(point))
            try:direct=[value(s,point) for s in signatures];integrated=[chamber(s,point) for s in signatures]
            except ZeroDivisionError:continue
            assert direct==integrated;break
        else:raise AssertionError('no regular chamber point')
        exact=dag.evaluate(point)
        for signature,got in zip(signatures,exact):
            brute=sum((value(signature,[point[i] for i in pi]) for pi in permutations(range(n))),Q(0))
            assert got==brute
        assert dag.evaluate(point,P)==[v.numerator%P*pow(v.denominator%P,-1,P)%P for v in exact]
        records.append(dict(n=n,signatures=signatures,point=point,exact_chamber_controls=6,exact_permutation_controls=6))
    out=dict(status='EXACT_WEIGHTED_PATH_DP_AND_CHAMBER_CONTROLS_PASS',records=records,producer_sha256=sha(Path(__file__)))
    (HERE/'overnight_upper_weighted_paths_controls.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],flush=True)


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def probe(n,mode):
    started=time.monotonic();signatures=family(n,mode);dag=Compiler(n).compile(signatures)
    stem=HERE/f'overnight_upper_weighted_paths_{mode}_{n}';binary=stem.with_suffix('.bin');dag.save(binary)
    print('DAG',mode,n,'COLUMNS',len(signatures),'STATES',len(dag.starts)-1,'TERMS',len(dag.left),'SECONDS',time.monotonic()-started,flush=True)
    rng=random.Random(25102597);points=[];width=len(signatures);rows=width+32
    while len(points)<rows:
        pt=[rng.randrange(1,1000000) for _ in range(n-1)];pt.append(-sum(pt));rng.shuffle(pt)
        good=True
        for apex,a in enumerate(pt):
            ff=[x for i,x in enumerate(pt) if i!=apex];sums=[0]*(1<<(n-1))
            for mask in range(1,len(sums)):
                bit=mask&-mask;sums[mask]=sums[mask^bit]+ff[bit.bit_length()-1]
            if any((sums[s]+a*h)*(sums[s]+a*(h+w))%P==0 for s,h,w in dag.factor_keys):good=False;break
        if good:points.append(pt)
    pointfile=stem.with_suffix('.points.txt');pointfile.write_text(f'{rows} {n}\n'+''.join(' '.join(map(str,p))+'\n' for p in points))
    exe='/tmp/overnight_upper_weighted_paths';subprocess.run(['g++','-O3','-std=c++17',str(HERE/'overnight_upper_weighted_paths.cpp'),'-o',exe],check=True)
    native_started=time.monotonic();subprocess.run([exe,str(binary),str(pointfile),str(stem.with_suffix('.u32'))],check=True)
    native_seconds=time.monotonic()-native_started;matrix=np.fromfile(stem.with_suffix('.u32'),dtype=np.uint32).reshape(rows,width+1)
    assert list(map(int,matrix[0,:-1]))==dag.evaluate(points[0],P)
    rr,rank=nmod_mat(matrix.tolist(),P).rref();pivots=[next(j for j in range(width+1) if rr[i,j]) for i in range(rank)]
    target=width in pivots
    out=dict(status='MODULAR_DIAGNOSTIC_ONLY',n=n,mode=mode,prime=P,signatures=signatures,points=points,
             ranks=[rank-int(target),rank],states=len(dag.starts)-1,terms=len(dag.left),
             native_seconds=native_seconds,seconds=time.monotonic()-started,producer_sha256=sha(Path(__file__)),
             cpp_sha256=sha(HERE/'overnight_upper_weighted_paths.cpp'),matrix_sha256=sha(stem.with_suffix('.u32')),
             complete_python_row_control=True)
    if not target:out['coefficients_mod_prime']=[[j,int(rr[i,width])] for i,j in enumerate(pivots) if rr[i,width]]
    stem.with_suffix('.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('DONE',out['ranks'],'SECONDS',out['seconds'],flush=True)


if __name__=='__main__':
    if sys.argv[1]=='controls':controls()
    else:probe(int(sys.argv[2]),sys.argv[1])
