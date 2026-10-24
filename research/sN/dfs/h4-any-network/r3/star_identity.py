# Exact check: F(p,q) = sum_{i,j} (-1)^{i+j} C(p,i) C(q,j) relu(i-j).
# Star neuron U = relu( sum_{P} relu(x_p-x_0) - sum_{Q} relu(x_q-x_0) ).
# At a locality with T = {0} u A u B (A in P, B in Q, |A|=p, |B|=q) the
# m-th mixed difference (cube side 1) equals (-1)^m * F(p,q) (see notes).
from math import comb
def F(p,q):
    return sum((-1)**(i+j)*comb(p,i)*comb(q,j)*max(i-j,0) for i in range(p+1) for j in range(q+1))
for p in range(0,9):
    print(p, [F(p,q) for q in range(0,9)])
