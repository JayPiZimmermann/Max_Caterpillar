#!/usr/bin/env python3
"""Bounded recursive exact pole reduction of the endpoint4|5 residue.

Negative homogeneous degree plus vanishing complete principal parts proves
zero. We use only simple-pole nodes above dimension3; lower-dimensional
nodes are checked by exact common-denominator polynomial arithmetic.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import gzip,hashlib,json,math,os,resource,sys,time
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq,fmpq_mpoly_ctx,ctx

HERE=Path(__file__).parent;BASE=HERE/'overnight_uniform_endpoint_q2_dfs'
DEADLINE=0;MEMO={};EVENTS=[];CALLS=0


def normalize(form):
    form=tuple(Q(x)for x in form)
    if not any(form):return None,Q(0)
    denominator=math.lcm(*(x.denominator for x in form));integer=tuple(int(x*denominator)for x in form)
    g=math.gcd(*integer)
    if next(x for x in integer if x)<0:g=-g
    return tuple(x//g for x in integer),Q(g,denominator)


def clean(terms):
    total=Counter()
    for (num,power,den),coefficient in terms.items():
        if not coefficient:continue
        den=list(den)
        while power and num in den:den.remove(num);power-=1
        total[(num if power else None,power,tuple(sorted(den)))]+=coefficient
    total={key:Q(c)for key,c in total.items()if c}
    if total:
        first=next(iter(total.values()));total={key:c/first for key,c in total.items()}
    return total


def function_hash(terms,frequency,free,cells):
    payload=(sorted((str(key),str(c))for key,c in terms.items()),frequency,free,cells)
    return hashlib.sha256(repr(payload).encode()).hexdigest()


def restriction(form,alpha,pivot):
    return normalize(tuple(Q(form[j])-Q(form[pivot])*alpha[j]/alpha[pivot]for j in range(len(alpha))if j!=pivot))


def residue(terms,alpha,pivot):
    answer=Counter();cache={}
    for (num,power,den),coefficient in terms.items():
        multiplicity=den.count(alpha)
        if not multiplicity:continue
        if multiplicity!=1:return None
        if power:
            newnum,scale=restriction(num,alpha,pivot)
            if newnum is None:continue
            coefficient*=scale**power
        else:newnum=None
        newden=[]
        for form in den:
            if form==alpha:continue
            if form not in cache:cache[form]=restriction(form,alpha,pivot)
            factor,scale=cache[form];assert factor is not None
            newden.append(factor);coefficient/=scale
        answer[(newnum,power,tuple(sorted(newden)))]+=coefficient
    return clean(answer)


def polynomial_zero(terms,dimension):
    context=fmpq_mpoly_ctx.get(tuple('x'+str(i)for i in range(dimension)));variables=context.gens()
    allfactors=Counter()
    for num,power,den in terms:allfactors|=Counter(den)
    forms={f:sum((c*x for c,x in zip(f,variables)),context.constant(0))for f in allfactors}
    numerator=context.constant(0)
    for (num,power,den),coefficient in terms.items():
        term=context.constant(fmpq(coefficient.numerator,coefficient.denominator))
        if power:term*=sum((c*x for c,x in zip(num,variables)),context.constant(0))**power
        for form,multiplicity in(allfactors-Counter(den)).items():term*=forms[form]**multiplicity
        numerator+=term
    return numerator==0,len(allfactors),sum(allfactors.values())


def pole_orbits(used,frequency,free,cells):
    generators=[(cell[i],cell[i+1])for cell in cells for i in range(len(cell)-1)]
    pending=set(used);orbits=[]
    while pending:
        first=min(pending,key=lambda f:(used[f],f));seen={first};queue=[first]
        for form in queue:
            full=dict(zip(free,form))
            for u,v in generators:
                coefficient=full.get(u,0)-full.get(v,0)
                if not coefficient:continue
                transformed,_=normalize(tuple(form[j]+coefficient*(frequency[v][j]-frequency[u][j])for j in range(len(free))))
                assert transformed is not None
                if transformed not in seen:seen.add(transformed);queue.append(transformed)
        present=seen&pending;pending-=seen
        orbits.append((first,len(seen),len(present),not seen<=used.keys()))
    return orbits


def solve(terms,frequency,free,cells,depth=0):
    global CALLS
    terms=clean(terms)
    if not terms:return True
    if time.monotonic()>DEADLINE:return None
    signature=function_hash(terms,frequency,free,cells)
    if signature in MEMO:return MEMO[signature]
    CALLS+=1;dimension=len(free)
    assert all(power-len(den)<0 for num,power,den in terms)
    if dimension<=3:
        zero,forms,degree=polynomial_zero(terms,dimension)
        EVENTS.append(dict(hash=signature,depth=depth,dimension=dimension,records=len(terms),
                           method='exact_common_denominator',forms=forms,degree=degree,zero=zero))
        MEMO[signature]=zero
        if not zero:print('EXACT NONZERO',EVENTS[-1],flush=True)
        return zero
    used=Counter(form for num,power,den in terms for form in den)
    if any(max(Counter(den).values(),default=0)>1 for num,power,den in terms):
        EVENTS.append(dict(hash=signature,depth=depth,dimension=dimension,records=len(terms),method='unresolved_multiple_pole'))
        return None
    tests=[]
    for alpha,size,present,missing in pole_orbits(used,frequency,free,cells):
        if time.monotonic()>DEADLINE:return None
        if missing:tests.append(dict(pole=alpha,orbit=size,method='symmetry_missing_pole'));continue
        pivot=next(i for i,c in enumerate(alpha)if c)
        child=residue(terms,alpha,pivot);assert child is not None
        newfrequency=[tuple(Q(f[j])-Q(f[pivot])*alpha[j]/alpha[pivot]for j in range(dimension)if j!=pivot)for f in frequency]
        newfree=free[:pivot]+free[pivot+1:]
        full=dict(zip(free,alpha));newcells=[]
        for cell in cells:
            for value in sorted({full.get(v,0)for v in cell}):newcells.append(tuple(v for v in cell if full.get(v,0)==value))
        result=solve(child,newfrequency,newfree,newcells,depth+1)
        tests.append(dict(pole=alpha,orbit=size,child_records=len(child),zero=result))
        if result is not True:
            EVENTS.append(dict(hash=signature,depth=depth,dimension=dimension,records=len(terms),method='pole_recursion',tests=tests,zero=result))
            if result is False:MEMO[signature]=False
            return result
    MEMO[signature]=True
    EVENTS.append(dict(hash=signature,depth=depth,dimension=dimension,records=len(terms),method='complete_pole_orbits',tests=tests,zero=True))
    if CALLS%10==0:print('proved nodes',len(MEMO),'calls',CALLS,'depth',depth,'dimension',dimension,flush=True)
    return True


def main(k=4):
    global DEADLINE,MEMO,BASE
    BASE=HERE/f'overnight_uniform_endpoint_q2_dfs_{k}'
    ctx.threads=1;resource.setrlimit(resource.RLIMIT_AS,(3*2**30,3*2**30));started=time.monotonic();DEADLINE=started+95
    memo_file=Path(str(BASE)+'.memo.json')
    file=HERE/f'overnight_uniform_endpoint_q2_residue_{k}.fractions.json.gz';data=json.load(gzip.open(file,'rt'))
    source_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();input_hash=hashlib.sha256(file.read_bytes()).hexdigest()
    if memo_file.exists():
        saved=json.loads(memo_file.read_text())
        if saved.get('source_sha256')==source_hash and saved.get('input_sha256')==input_hash:MEMO=saved['nodes']
    forms=[tuple(f)for f in data['linear_forms']]
    terms={(forms[r['numerator']],4,tuple(forms[j]for j in r['denominator'])):Q(r['coefficient'])for r in data['records']}
    frequency=[tuple(map(Q,f[:7]))for f in data['frequency_chart']];free=list(range(k-1))+list(range(k,8));cells=[tuple(range(k)),tuple(range(k,9))]
    result=solve(terms,frequency,free,cells)
    memo_file.write_text(json.dumps(dict(source_sha256=source_hash,input_sha256=input_hash,nodes=MEMO),sort_keys=True)+'\n')
    out=dict(status='BOUNDED_EXACT_RECURSIVE_POLE_CERTIFICATION',zero=result,completed_nodes=len(MEMO),calls_this_phase=CALLS,
             seconds=time.monotonic()-started,events=EVENTS,input_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='Only the specified ordinary-cut residue of the sampled36-term relation is tested. A successful recursion still requires independent review; other first-pole types remain separate obligations.')
    Path(str(BASE)+'.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k!='events'},indent=2),flush=True)


if __name__=='__main__':main(int(sys.argv[1])if len(sys.argv)>1 else 4)
