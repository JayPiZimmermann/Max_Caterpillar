# Natural eight-row first hidden layer: five free outer terms are impossible

**Analytic result, independently reviewed:** the natural six invariant
features require at least six free outer ReLUs, even after allowing an
arbitrary linear remainder in those features. With the established
translation-carrier bridge, the natural eight-row first hidden layer
therefore requires second hidden layer width at least eight. In particular,
there is no matching `(8,7)` construction.

The geometric proof below has no finite coefficient search or numerical
assumption. A separate Lean leaf verifies its final linear-inequality
contradiction. The network-to-corner reduction is proved here, not yet in
Lean. This remains research-only until there is a matching construction.

## Exact model and the four full corner cones

Let

\[
 (a,b,c)=(\sigma(u),\sigma(v),\sigma(v-u)),\qquad
 (d,e,f)=(\sigma(s),\sigma(t),\sigma(t-s)).
\]

The first block image is the union of the three two-dimensional cones
between consecutive rays

\[
 r_0=(1,0,0),\quad r_1=(1,1,0),\quad
 r_2=(0,1,1),\quad r_3=(0,0,1).
\]

Its maximum has values `(1,1,1,0)` on these rays. The target on the product
image is

\[
 F(a,b,c,d,e,f)=\max(a,b,d,e).
\]

Suppose it has a representation by at most five outer ReLUs of linear
forms in the six features, plus an arbitrary linear remainder. Biases,
if allowed, can first be removed by taking recession functions.

It is enough to use the four corner products of the first and last cones:

| Cone | First block | Second block | Target |
|---|---|---|---|
| `00` | `c=0, a>=b>=0` | `f=0, d>=e>=0` | `max(a,d)` |
| `02` | `c=0, a>=b>=0` | `d=0, f>=e>=0` | `max(a,e)` |
| `20` | `a=0, c>=b>=0` | `f=0, d>=e>=0` | `max(b,d)` |
| `22` | `a=0, c>=b>=0` | `d=0, f>=e>=0` | `max(b,e)` |

These are full four-dimensional cones relative to their linear spans.
In particular, **both `b` and `e` are independent coordinates on every
corner span**. The argument uses their full interiors, not just the
sixteen two-dimensional ray quadrants refuted as a sufficient test in
`overnight_fixed_rayplane_obstruction.md`.

## Four distinct positive carriers are necessary

A target crease on a corner must receive a positive contribution from an
outer ReLU whose restricted linear form is proportional to the target
normal. A linear form cannot carry target creases on two different
corners. One way to see this is the ray circuit

\[
 \alpha_0-\alpha_1+\alpha_2-\alpha_3=0.
\]

Carrying the target on first-block cone `0` forces
`alpha0=alpha1!=0`; carrying it on cone `2` forces
`alpha2!=0, alpha3=0`, which violates the circuit. The analogous argument
applies to the second block. Equivalently, the normal forms below have
incompatible `b,e` coefficients at different corners.

Choose one positive-output carrier for each corner. Flip its input sign
if necessary, absorbing the resulting linear function into the remainder,
and absorb its positive output magnitude into the input form. The four
positive terms then have forms

\[
\begin{aligned}
 p_{00}&=t_0a+A c-t_0d+B f,\\
 p_{02}&=t_1a+C c+D d-t_1e,\\
 p_{20}&=E a+t_2b-t_2d+K f,\\
 p_{22}&=G a+T b+H d-T e,
\end{aligned}
\]

with all carrier amplitudes `t0,t1,t2,T` strictly positive.

At every corner, the three foreign carrier normals are pairwise
nonproportional, and are not proportional to the target normal. Their
`b,e` coefficient patterns are respectively

\[
 (0,0),\quad(0,-t_1),\quad(t_2,0),\quad(T,-T).
\]

The zero-pattern distinctions survive every corner restriction because
`b,e` remain independent there. The first form can never become
proportional to a form with a nonzero `b` or `e` coefficient. The other
three have different nonzero-coordinate patterns.

The carrier `p22` cannot have fixed sign on all three foreign corners:
fixed sign on `02` requires `G<=-T`, while fixed sign on `20` requires
`H>=T`. Those inequalities force it to cross the interior of `00`.
Therefore its foreign crease needs a negative output term. There are at
most five terms total, so the entire representation has precisely the
four positive carriers and one negative term `-sigma(h)`.

## The negative term can cancel only the last carrier

At a foreign corner where `p22` crosses, no other positive carrier shares
its hyperplane. Its cancellation therefore forces the restriction of
`h` to equal `p22` or `-p22`. There is no free proportionality factor:
all output magnitudes have already been absorbed into the preactivations,
and equality of crease magnitudes gives absolute factor one.

It follows that the global `b,e` coefficients of `h` are `(T,-T)` or
`(-T,T)`. Flip `h` if needed, again adjusting only the linear remainder,
to take the first choice. Thus `h` cannot cancel any of the other three
carriers on any corner: each of them has a zero coefficient in at least
one of `b,e`.

On corner `22`, `h` cannot cross the interior. A foreign crease would
have no possible cancellation. If its crease were the target crease,
its `b,e` coefficients force its restriction to equal `T(b-e)`, cancelling
`p22` completely and leaving no target crease. Hence `h` has fixed sign
on `22`, and the target jump forces `T=1`.

Write

\[
 p=p_{22}=G a+b+H d-e,\qquad
 h=x a+b+s c+z d-e+v f.
\]

On each foreign corner, either both forms have fixed sign, or their
restrictions agree. These are the only ways the crease of
`sigma(p)-sigma(h)` can disappear.

## Two sign cases give the contradiction

If `h>=0` on corner `22`, its extreme-ray values give `s>=0, v>=1`.
On `02`, `p` can only have fixed negative sign or cross, while `h` can
only have fixed positive sign or cross. Equal crossing restrictions
would require `v=0`, impossible. Thus

\[
 G\le-1,\qquad x\ge0.
\]

On `00`, equality of crossing restrictions would require `x=G`, also
impossible. Hence both restrictions have fixed sign, forcing

\[
 H\le0,\qquad z\ge1.
\]

But `p` now crosses `20`, so equality of restrictions there forces
`z=H`, a contradiction.

If `h<=0` on corner `22`, its ray values give `s<=-1, v<=0`.
Corner `20` first forces `H>=1, z<=0`; corner `00` then forces
`G>=0, x<=-1`; and the crossing on `02` forces `x=G`, again a
contradiction. Weak inequalities include all boundary and degenerate
fixed-sign cases.

Thus no representation with five or fewer free outer terms exists.

## Verification and width scope

The independent conceptual review by the general-bound agent checked the
carrier assignment, the independent `b,e` coordinates on all four spans,
the sign-flip normalization, the cancellation amplitudes, and both final
sign chains. No gap was found.

`overnight_fixed_natural8_five_corner.lean` verifies the final incompatibility
of the four normalized sign/equality conditions over arbitrary real
coefficients. Its declared scope is only that algebraic core; the present
note supplies the geometric reduction. The Lean axiom receipt is stored
in the adjacent `.log`.

The established fixed-first-layer translation-carrier bridge gives
`h2=k_W+2`, so the result is `h2>=8` for the natural eight-row layer. The
independently checked classification in
`../frontierN/overnight_general_six.md` says every unrestricted `h1=8`
representation has this layer, up to scaling, permutation, and choices
of matching-edge orientation. Swapping the two coordinates of a block
covers the orientation choices. Thus the two results together imply
`h1=8 => h2>=8` in the original arbitrary-real network model.

The next constructive target is six free terms on all nine product cones,
which would give a matching `(8,8)` network. The earlier localized
four-ReLU blocks and the collective overlap counterexample remain useful
controls; this proof does not claim that arbitrary-width shallow
completion of the natural eight-row layer is impossible.
