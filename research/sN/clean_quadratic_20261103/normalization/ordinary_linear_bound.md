# An elementary linear bound for the ordinary architecture

This is a separately audited mathematical argument, not yet a Lean theorem
in this directory. It is not needed for the fixed-C existential paper proof:
there the trivial bound h2>=1 absorbs finitely many small dimensions.

**Claim.** Every ordinary two-hidden-layer ReLU representation of MAX_N,
with arbitrary real biases and no skip connections, satisfies

    h2 >= ceil(N/2).

Remove all biases by the recession argument in normalization.md. Write the
homogeneous network as

    MAX_N(x)=sum_{k=1}^{h2} d_k sigma(g_k(x)),
    g_k(x)=sum_j W_kj sigma(A_j x).

The scalar identity sigma(t)-sigma(-t)=t shows

    g_k(x)-g_k(-x)=u_k x,  where u_k=sum_j W_kj A_j.

Let V be the common kernel of the h2 forms u_k. Then dim V>=N-h2. Every
g_k is even on V, so MAX_N is even on V as well.

Let p_i be the i-th coordinate functional restricted to V and put
P=conv{p_1,...,p_N} in V*. Its support function is MAX_N|_V. Evenness of this
support function implies P=-P. The coordinate restrictions span V*, so P
is a full-dimensional centrally symmetric polytope. Its vertices occur in
opposite pairs. Choosing one representative from each pair still spans V*,
and therefore P has at least 2 dim V vertices. Since P is the convex hull of
N points, it has at most N vertices. Consequently

    N >= 2 dim V >= 2(N-h2),

which proves the claim.

The support-function fact used above is elementary: two compact convex sets
with the same support function are equal. If a point p of one were outside
the other, choose a nearest point q of the latter. The vector p-q strictly
separates p from that set, contradicting equality of support functions.

The argument specifically concerns the ordinary architecture: free output
linear or shallow terms alter the evenness equation on V. Applying it after
introducing normalization's internal shallow terms would therefore be wrong.
Apply it directly to the bias-free ordinary network.

Independent mathematical audit: subagent audit_bias_limits checked the
recession step, the odd-part identity, the subspace dimension, and the
centrally symmetric polytope count on 2026-11-03.
