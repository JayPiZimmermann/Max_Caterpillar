# Closing the two-comparison-form extension, with a free remainder

The following entire real-parameter family fails on the certified seven
P4 features `z=(sigma(u),sigma(v),sigma(v-u),sigma(s),sigma(t),sigma(s-t),sigma(v-t))`:

\[
 R(z)+\sigma(L(z))-\sigma(M(z))
 +\tfrac12\sigma(b-a+d-c)+\tfrac12\sigma(b-a+c-d),
\]

where `R,L,M` are arbitrary linear forms and
`a=sigma(u),b=sigma(v),c=sigma(s),d=sigma(t)`.
This is a family exclusion, not a lower bound for arbitrary four-free-term
representations. It supersedes the bounded diagnostic for this same family.

On strictly positive inputs write

\[
 L_0=\max(s,t)-\max(u,v),\qquad
 M_0=(|s-t|-|u-v|)/2.
\]

The desired residual after the two fixed symmetric terms is
`a+sigma(L0)-sigma(M0)`. Consider three open cells of the first-feature
arrangement:

| Cell | Strict conditions | `L0` | `M0` |
|---|---|---|---|
| 1 | `u<v, s>t, v>t`, all positive | `s-v` | `(u-v+s-t)/2` |
| 2 | `u>v, s>t, v>t`, all positive | `s-u` | `(-u+v+s-t)/2` |
| 3 | `u>v, s<t, v<t`, all positive | `t-u` | `(-u+v-s+t)/2` |

Both distinct hyperplanes `L0=0` and `M0=0` cross every cell's interior.
Explicit points on them, respectively, are `(1,3,3,2)` and `(1,3,4,2)`
for cell1, `(3,2,3,1)` and `(4,2,3,1)` for cell2, and `(3,1,2,3)` and
`(3,1,2,4)` for cell3. At each point the other form is nonzero.

The positive and negative jumps force `L=±L0` and `M=±M0` on each
cell. The free remainder cannot change this assertion because it is
linear on that cell. Each comparison form is linear in the seven features,
so its four input-gradient equations on each cell must be compatible.
They force the sign choices to agree across all three cells and give

\[
 L=\pm(-a-p+d+q),\qquad
 M=\pm((-a+b-c+d)/2-p+q),
\]

where `p=sigma(v-u),q=sigma(s-t)`. In particular, both coefficients of
the extra feature `r=sigma(v-t)` vanish. The three cell maps together
have rank seven, so the remainder is uniquely determined. It merely
absorbs either global sign flip using `sigma(-g)=sigma(g)-g`.
All four candidates therefore represent the same global function.

At `(u,v,s,t)=(4,4,2,-1)` that function equals three, whereas the target
is four. This proves the exclusion with arbitrary real coefficients and
an arbitrary feature-linear remainder.

`overnight_fixed_p4_twoargs_geometry.py` checks the eight sign choices for
each form by exact rational elimination, finding only the two global
signs. It builds all four normalized networks, evaluates the exact
counterexample for each, and also runs the independent global cone
checker, which rejects all four. No coefficient bound or numerical solver
is part of this argument. The written crease-uniqueness reduction supplies
the finite sign-domain bridge; this is not a Lean theorem.

Further searches should change the two fixed symmetric terms themselves.
Merely freeing their two comparison arguments, their linear remainder,
or the global preactivation orientations cannot repair this template.
