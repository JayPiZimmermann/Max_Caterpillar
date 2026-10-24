import itertools, random, math, sys
from hill import W
n=int(sys.argv[1]); random.seed(int(sys.argv[2])); iters=int(sys.argv[3])
edges=list(itertools.combinations(range(n),2))
s,f0=0,1
c={e:(1 if s in e else 0) for e in edges}
gam=[0]*n; gam[f0]=-2; gam[s]=2-(n-1)
f=W(n,c,gam)/math.factorial(n-3); print("star f",f,flush=True)
best=f
for r in range(iters):
    cc,gg,ff=dict(c),list(gam),f
    for step in range(200):
        c2=dict(cc); g2=list(gg)
        for _ in range(random.randint(1,3)):
            if random.random()<0.5: e=random.choice(edges); c2[e]=max(0,c2[e]+random.choice([-1,1]))
            else: i=random.randrange(n); g2[i]+=random.choice([-1,1])
        f2=W(n,c2,g2)/math.factorial(n-3)
        if f2>=ff-0.5*(random.random()<0.1): cc,gg,ff=c2,g2,f2
        if ff>best: best=ff; print("NEW",best,cc,gg,flush=True)
print("best",best)
