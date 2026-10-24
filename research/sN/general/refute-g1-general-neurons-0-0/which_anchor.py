"""For the paper's cube functional Delta_rho, test each anchor position (index i in sorted T) across all m-sets."""
import itertools,sys
relu=lambda t: t if t>0 else 0
N=int(sys.argv[1])
from collections import Counter
fail=Counter(); cnt=Counter()
for m in range(3,N+1):
  for T in itertools.combinations(range(N),m):
    for i,a in enumerate(T[1:-1],1):
      D=0
      for eps in itertools.product((0,1),repeat=m):
        S={t for e,t in zip(eps,T) if e}
        G=0 if a in S else sum((2**t if t>a else -2**t) for t in S)
        D+=(-1)**(m-len(S))*relu(G)
      cnt[(m,i)]+=1; fail[(m,i)]+=(D==0)
for k in sorted(cnt): print('m,pos',k,'fail',fail[k],'/',cnt[k])
