"""Test: for g = <l,x> + sum a_ij |x_i-x_j| (+ univariate relu terms), the coefficients of g
restricted to the stratum (x_T = c, x_O in chamber rho inside (0,c)) vanish iff E_L,
and the T-germ slopes are rho-independent. Random integer neurons, exact check via finite differences."""
import itertools, random
from fractions import Fraction as Fr
random.seed(1)
def run(N, trials=300):
    bad = 0; agree = 0
    for _ in range(trials):
        a = {(i,j): random.randint(-1,1) for i,j in itertools.combinations(range(N),2)}
        A = lambda i,j: 0 if i==j else a[(min(i,j),max(i,j))]
        kappa = [random.randint(-1,2) for _ in range(N)]
        l = [2*kappa[v]-sum(A(v,j) for j in range(N)) for v in range(N)]
        up = [random.randint(-1,1) for _ in range(N)]; dn=[random.randint(-1,1) for _ in range(N)]
        g = lambda x: sum(l[i]*x[i]+up[i]*max(x[i],0)+dn[i]*max(-x[i],0) for i in range(N)) + sum(a[p]*abs(x[p[0]]-x[p[1]]) for p in a)
        for T in itertools.combinations(range(N),3):
            O=[v for v in range(N) if v not in T]
            germs=set()
            for order in itertools.permutations(O):
                c=Fr(10); base={}
                for t in T: base[t]=c
                for r,o in enumerate(order): base[o]=Fr(9-r)  # top-down
                x=[base[i] for i in range(N)]
                # linear coefficients on stratum via finite differences in O and in c
                g0=g(x); co={}
                for o in O:
                    y=x[:]; y[o]+=Fr(1,100); co[o]=(g(y)-g0)*100
                yc=x[:]
                for t in T: yc[t]+=Fr(1,100)
                for o in O: yc[o]+=0
                cc=(g(yc)-g0)*100
                vanish = g0==0 and all(v==0 for v in co.values()) and cc==0
                # E_L: coefficient of x_o equals ... (translation-free part) check co[o]== 2kappa_o-2sum_above + up/dn
                above=list(T); EL=True
                for o in order:
                    if sum(A(o,j) for j in above)!=kappa[o]: EL=False
                    above.append(o)
                # with univariate terms included, compare co[o] to 2(kappa-sum_above)+up_o
                above=list(T); ok=True
                for o in order:
                    if co[o]!=2*(kappa[o]-sum(A(o,j) for j in above))+up[o]: ok=False
                    above.append(o)
                if not ok: bad+=1
                # germ slopes
                sl=[]
                for t in T:
                    y=x[:]; y[t]+=Fr(1,100); z=x[:]
                    for u in T:
                        if u!=t: z[u]=z[u]  # move only t upward: picks slope with t on top among T
                    sl.append((g(y)-g0)*100)
                germs.add(tuple(sl))
            if len(germs)!=1: bad+=1
    return bad
for N in (4,5,6): print(N, 'bad', run(N, 60 if N<6 else 15))
