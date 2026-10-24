# Independent check: g = b + <l,x> + sum a_ij |x_i-x_j| (+ c_i sigma(x_i) + e_i sigma(-x_i)),
# require g(p)=0 at exact rational points p in W_T={x_T tied = t > x_o} (positive orthant), all T, random orders.
import itertools, random, sys
from sympy import Matrix, Rational
N=int(sys.argv[1]); random.seed(1)
pairs=list(itertools.combinations(range(N),2))
def row(p):
    r=[1]+list(p)+[abs(p[i]-p[j]) for i,j in pairs]+[max(v,0) for v in p]+[max(-v,0) for v in p]
    return r
rows=[]
for T in itertools.combinations(range(N),3):
    O=[o for o in range(N) if o not in T]
    for perm in itertools.permutations(O):
        for _ in range(3):
            t=Rational(random.randint(100,200))
            hs=sorted(Rational(random.randint(1,90),random.randint(1,7)) for _ in O)
            if len(set(hs))<len(hs): continue
            p=[None]*N
            for i in T: p[i]=t
            for o,h in zip(perm,hs): p[o]=t-h
            rows.append(row(p))
M=Matrix(rows); ns=M.nullspace()
print("N",N,"unknowns",M.cols,"rows",M.rows,"nullity",len(ns))
# nullspace vectors should only be the trivial ones: sigma(x_i)-sigma(-x_i)-x_i = 0 identity
for v in ns: print(list(v.T))
