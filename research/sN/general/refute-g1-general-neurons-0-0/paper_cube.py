"""Paper's functional Delta_rho: cube p + delta*1_S, positive steps, at the stratum point.
For g_a (a interior of T), germ G(delta 1_S) = delta*sum_{t in S\a} c_t if a not in S else 0.
Count, for each m-set T, which interior anchors a give Delta != 0, and whether some does."""
import itertools,sys
relu=lambda t: t if t>0 else 0
for N in range(3,int(sys.argv[1])+1):
  zeroT=0; zeroPairs=0; tot=0; allT=0
  for m in range(3,N+1):
    for T in itertools.combinations(range(N),m):
      allT+=1; anyok=False
      for a in T[1:-1]:
        tot+=1
        D=0
        for eps in itertools.product((0,1),repeat=m):
          S={t for e,t in zip(eps,T) if e}
          G=0 if a in S else sum((2**t if t>a else -2**t) for t in S)
          D+=(-1)**(m-len(S))*relu(G)
        if D==0: zeroPairs+=1
        else: anyok=True
      if not anyok: zeroT+=1
  print(N,'(T,a) pairs',tot,'zero Delta',zeroPairs,'| m-sets',allT,'with no passing anchor',zeroT)
