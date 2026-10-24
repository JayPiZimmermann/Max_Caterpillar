#!/usr/bin/env python3
"""Fixed-cycle top-class experiment. Exact controls and budgeted modular probes.

Inner graphs omit the apex. Tree atom head h has sum zero, h[apex]=-1.
Cycle tiling is independent of the chamber-integral control implementation.
"""
import itertools, math, json, random, sys, time
from fractions import Fraction as Q
from pathlib import Path

P=1000003

def canonical(h,edges):
    h=list(h);ee=[]
    for u,v in edges:
        if u>v:h[u]+=1;h[v]-=1;u,v=v,u
        ee.append((u,v))
    return tuple(h),tuple(sorted(ee))

def permute(key,pi):
    h,es=key;hh=[0]*len(h)
    for j,x in enumerate(h):hh[pi[j]]=x
    return canonical(hh,[(pi[u],pi[v]) for u,v in es])

def cuts(key,apex):
    h,es=key;out=[]
    for u,v in es:
        seen={u};todo=[u]
        while todo:
            w=todo.pop()
            for x,y in es:
                if (x,y)==(u,v):continue
                z=y if x==w else x if y==w else None
                if z is not None and z not in seen:seen.add(z);todo.append(z)
        assert v not in seen
        out.append((tuple(sorted(seen)),sum(h[i] for i in seen)))
    return out

def tree_value(key,apex,om):
    n=len(om);a=om[apex];den=1
    for side,H in cuts(key,apex):
        q=sum(om[i] for i in side);den*=(q+a*H)*(q+a*(H+1))
    return Q((-a)**(n-4),den)

def chamber_value(key,om):
    h,edges=key;n=len(h);d=n-1;out=Q(0)
    for pi in itertools.permutations(range(n)):
        pos={v:j for j,v in enumerate(pi)};aa=list(h)
        for u,v in edges:
            if pos[u]<pos[v]:aa[u]+=1;aa[v]-=1
        A=[];O=[];a=o=0
        for v in pi[:-1]:
            a+=aa[v];o+=om[v];A.append(a);O.append(o)
        for j in range(d):
            if A[j]<=0:continue
            den=O[j]**2
            for k in range(d):
                if j!=k:den*=A[j]*O[k]-A[k]*O[j]
            out+=Q(A[j]**d,den)
    return out

def cycle_atoms(h,edges):
    # edges are a consistently directed simple cycle; sum e_u-e_v = 0.
    return [canonical(h,edges[:j]+edges[j+1:]) for j in range(len(edges))]

def family(n):
    out={}
    for apex in range(n):
        vv=[i for i in range(n) if i!=apex];cycle=list(zip(vv,vv[1:]+vv[:1]));m=n-1
        for root in vv:
            base=[0]*n;base[root]=1;base[apex]=-1
            for mask in range(1<<m):
                ee=[(v,u) if mask>>j&1 else (u,v) for j,(u,v) in enumerate(cycle)]
                key=canonical(base,ee)
                if key not in out:
                    h=list(base)
                    for j,(u,v) in enumerate(cycle):
                        if mask>>j&1:h[u]-=1;h[v]+=1
                    out[key]=(apex,cycle_atoms(h,cycle))
            for missing in range(m):
                u,v=cycle[missing];rest=cycle[:missing]+cycle[missing+1:]
                for state in (-1,0,1):
                    h=list(base);h[u]+=state;h[v]-=state
                    for mask in range(1<<(m-1)):
                        ee=[(y,x) if mask>>j&1 else (x,y) for j,(x,y) in enumerate(rest)]
                        key=canonical(h,ee)
                        out.setdefault(key,(apex,[key]))
    return out

def control():
    rng=random.Random(24102411);records=[]
    for n in (4,5):
        for j in range(8):
            apex=n-1;vs=list(range(n-1));edges=list(zip(vs,vs[1:]));h=[rng.randrange(-2,3) for _ in range(n-2)];h+=[1-sum(h),-1]
            key=canonical(h,[(v,u) if rng.randrange(2) else (u,v) for u,v in edges])
            cyc=list(zip(vs,vs[1:]+vs[:1]));hc=[0]*n;hc[j%(n-1)]=1;hc[apex]=-1
            oriented=[(v,u) if rng.randrange(2) else (u,v) for u,v in cyc]
            ht=list(hc)
            for (u,v),e in zip(cyc,oriented):
                if e!=(u,v):ht[u]-=1;ht[v]+=1
            ck=canonical(hc,oriented)
            for attempt in range(100):
                om=[rng.randrange(1,100000) for _ in range(n-1)];om+=[-sum(om)];rng.shuffle(om)
                try:
                    a=tree_value(key,apex,om);b=chamber_value(key,om)
                    c=sum((tree_value(t,apex,om) for t in cycle_atoms(ht,cyc)),Q(0));d=chamber_value(ck,om)
                    break
                except ZeroDivisionError:continue
            assert a==b,(n,j,a,b)
            assert c==d,(n,j,c,d)
            # A deliberately omitted tile should differ generically.
            assert tree_value(cycle_atoms(ht,cyc)[0],apex,om)!=0
            records.append(dict(n=n,head=key[0],tree=key[1],cycle=ck,frequency=om,tree_value=str(a),cycle_value=str(c)))
    data=dict(status='EXACT_RATIONAL_POINT_CONTROLS_NOT_UNIFORM_IDENTITY',cases=records)
    Path(__file__).with_name('controls.json').write_text(json.dumps(data,indent=2)+'\n')
    print('PASS',len(records),'general-head tree and cycle/chamber exact controls',flush=True)

def probe(n,budget=180):
    import numpy as np
    start=time.time();ff=family(n);keys=list(ff);index={k:i for i,k in enumerate(keys)}
    orbits=[];seen=set()
    for i,k in enumerate(keys):
        if i in seen:continue
        orb=sorted({index[permute(k,[(sg*j+a)%n for j in range(n)])] for sg in (-1,1) for a in range(n)})
        seen.update(orb);orbits.append(orb)
    print('N',n,'units',len(ff),'orbits',len(orbits),'generation',time.time()-start,flush=True)
    atoms={};unitatoms=[]
    for k in keys:
        a,aa=ff[k];li=[]
        for atom in aa:
            ka=(a,atom)
            if ka not in atoms:atoms[ka]=len(atoms)
            li.append(atoms[ka])
        unitatoms.append(li)
    at=list(atoms);cs=[cuts(k,a) for a,k in at]
    masks=np.array([[sum(1<<v for v in side) for side,H in c] for c in cs],dtype=np.int64)
    hs=np.array([[H for side,H in c] for c in cs],dtype=np.int64)
    ap=np.array([a for a,k in at],dtype=np.int64)
    membership=np.array([[mask>>v&1 for v in range(n)] for mask in range(1<<n)],dtype=np.int64)
    # Combine the atom multiplicities directly into each dihedral orbit column.
    inds=[];offset=[]
    for orb in orbits:
        offset.append(len(inds))
        for i in orb:inds.extend(unitatoms[i])
    inds=np.array(inds,dtype=np.int64)
    inv=np.zeros(P,dtype=np.int64);inv[1]=1
    for j in range(2,P):inv[j]=P-(P//j)*inv[P%j]%P
    rng=random.Random(24102411);basis={};rows=[];pts=[];compute=time.time();bad=0;m=len(orbits)
    for count in range(m+25):
        while True:
            pt=[rng.randrange(1,10000) for _ in range(n-1)];pt.append(-sum(pt));rng.shuffle(pt)
            om=np.array(pt,dtype=np.int64)%P;aa=om[ap];qs=(membership@om)[masks]%P
            den=np.ones(len(at),dtype=np.int64)
            for j in range(n-2):
                den=den*((qs[:,j]+aa*hs[:,j])%P)%P
                den=den*((qs[:,j]+aa*(hs[:,j]+1))%P)%P
            if np.all(den) and math.prod(pt)%P:break
            bad+=1
        numer=np.ones(len(at),dtype=np.int64)
        for _ in range(n-4):numer=numer*(-aa)%P
        vals=numer*inv[den]%P;row=np.add.reduceat(vals[inds],offset)%P
        target=(-1)**(n-1)*int(inv[math.prod(pt)%P])%P
        v=np.r_[row,target];rows.append([int(x) for x in v]);pts.append(pt)
        for j,b in sorted(basis.items()):v=(v-v[j]*b)%P
        nz=np.flatnonzero(v)
        if len(nz):j=int(nz[0]);basis[j]=v*inv[v[j]]%P
        if (count+1)%50==0:print('rows',count+1,'ranks',len(basis)-int(m in basis),len(basis),'seconds',time.time()-compute,flush=True)
        if time.time()-compute>budget:break
    ranks=[len(basis)-int(m in basis),len(basis)]
    data=dict(n=n,prime=P,seed=24102411,units=len(keys),atoms=len(at),orbits=orbits,keys=keys,points=pts,rows=rows,ranks=ranks,seconds=time.time()-start,rejected_pole_points=bad,status='MODULAR_DIAGNOSTIC_ONLY')
    if m not in basis:
        x=np.zeros(m+1,dtype=np.int64);x[-1]=-1
        for j,b in sorted(basis.items(),reverse=True):x[j]=-int(b@x)%P
        data['modular_coefficient_proposal']=[int(t) for t in x[:-1]]
    Path(__file__).with_name(f'cycle_probe_{n}.json').write_text(json.dumps(data)+'\n')
    print('DONE',n,'ranks',ranks,'rows',len(rows),'seconds',time.time()-start,flush=True)

if __name__=='__main__':
    if sys.argv[1]=='control':control()
    else:probe(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 180)
