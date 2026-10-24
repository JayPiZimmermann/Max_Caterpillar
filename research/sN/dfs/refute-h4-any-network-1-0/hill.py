# Independent check of F(n) <= n-2 (n=5,6) directly from the raw neuron definition:
# g = sum gamma_i x_i + sum_{i<j} c_e max(x_i,x_j); test zero on cell via coefficients,
# Lambda via brute 8-corner sum of sigma(g(p+z)) - sigma(g(p)), exact Fractions not needed (integers).
import itertools, random, sys
def W(n,c,gam):
    V=range(n); tot=0
    for T in itertools.combinations(V,3):
        O=[v for v in V if v not in T]
        for order in itertools.permutations(O):
            # heights: T at n, order[i] at n-1-i ; generic point
            def g(x): return sum(gam[i]*x[i] for i in V)+sum(c[(i,j)]*max(x[i],x[j]) for (i,j) in c)
            base=[0]*n
            for t in T: base[t]=10*n
            for k,o in enumerate(order): base[o]=10*(n-1-k)
            # zero on cell: check linear in (s,x_O): evaluate at base and perturbations
            pts=[base]
            b2=list(base); 
            for t in T: b2[t]+=1
            pts.append(b2)
            for o in O:
                b3=list(base); b3[o]+=1; pts.append(b3)
            if any(g(p)!=0 for p in pts): continue
            L=0
            for S in itertools.product([0,1],repeat=3):
                x=list(base)
                for t,s in zip(T,S): x[t]+=s
                L+=(-1)**(3-sum(S))*max(g(x),0)
            if L!=0: tot+=1
    return tot
import math
if __name__=="__main__":
  n=int(sys.argv[1]); iters=int(sys.argv[2]); random.seed(int(sys.argv[3]))
  edges=list(itertools.combinations(range(n),2))
  best=0
  for it in range(iters):
      c={e:random.choice([0,0,1,1,2,3]) for e in edges}
      gam=[random.randint(-8,2) for _ in range(n)]
      f=W(n,c,gam)/math.factorial(n-3)
      # local search
      for step in range(60):
          c2=dict(c); g2=list(gam)
          if random.random()<0.5: e=random.choice(edges); c2[e]=max(0,c2[e]+random.choice([-1,1]))
          else: i=random.randrange(n); g2[i]+=random.choice([-1,1])
          f2=W(n,c2,g2)/math.factorial(n-3)
          if f2>=f: c,gam,f=c2,g2,f2
      if f>best: best=f; print(it,best,c,gam,flush=True)
  print("best",best)
  