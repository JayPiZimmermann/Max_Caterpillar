# Paper's Delta_rho (cube +delta*1_S at tie value 0) applied to sigma(g_a), exact integers.
# Delta/delta = sum_{S subset T\a} (-1)^{m-|S|} relu(c(S)); corners containing a give G=0.
import itertools, sys
N=int(sys.argv[1]); zeros=[]; tot=0
for m in range(3,N+1):
  for T in itertools.combinations(range(N),m):
    for a in T[1:-1]:
      Tp=[t for t in T if t!=a]; c={t:(2**t if t>a else -2**t) for t in Tp}
      s=0
      for r in range(len(Tp)+1):
        for S in itertools.combinations(Tp,r):
          v=sum(c[t] for t in S); s+=(-1)**(m-r)*max(v,0)
      tot+=1
      if s==0: zeros.append((T,a))
  # does some interior a pass each T?
bad=[]
for m in range(3,N+1):
  for T in itertools.combinations(range(N),m):
    if all((T,a) in set(zeros) for a in T[1:-1]): bad.append(T)
print(N,"pairs",tot,"zero (T,a)",len(zeros),"T with no passing interior a",len(bad), bad[:5], zeros[:5])
