# A certified N=5 construction with first hidden layer width nine

There is a rational two-hidden-layer ReLU network of widths **(9,17)**
equal to `max(x_0,...,x_4)` on all of R^5. Its full coefficients are in
`overnight_fixed_cross_net9_17.json`. This improves the current upper
bound on the least possible first hidden layer width to nine. The
unrestricted lower bound is eight; existence at first width eight is
still open. Neither width in this new construction is asserted optimal.
The new result remains research-only, since no matching lower bound for
this particular first hidden layer has been established.

Put `u=x_1-x_0`, `v=x_2-x_0`, `s=x_3-x_0`, and `t=x_4-x_0`. The seven
translation-invariant functions in the first hidden layer are

    sigma(u), sigma(v), sigma(v-u), sigma(s), sigma(t),
    sigma(s-t), sigma(v-t).

The other two are `sigma(x_0),sigma(-x_0)`. The seven comparison edges
form a star centered at zero together with the path 1−2−4−3 on its
leaves. The edge orientation matters for the finite dictionary search.
No extension of this one fixed graph to arbitrary N is claimed.

## Exact global certificate

`overnight_fixed_cross_verify.py` is a standalone standard-library
checker. It imports no fitting code or LP solver. The network's first
two second-hidden-layer neurons are opposite preactivations with outputs
`+1,-1`, so their sum is exactly `x_0+R(Phi(x))` for a specified linear
combination R of the first seven functions. Every other outer
preactivation uses only those seven functions.

On a braid cone `x_pi(0)>...>x_pi(4)`, each comparison function is
linear. The checker computes each outer preactivation as an exact linear
form g in the original five input coordinates. Since g has coefficient
sum zero, its values on the four prefix-indicator generators determine
its sign on the entire cone. If they are all nonnegative, `sigma(g)=g`;
if all nonpositive, `sigma(g)=0`. Otherwise g has a hyperplane crossing
the interior.

Normalize the latter forms by their first nonzero coefficient. Group
proportional forms, and apply `sigma(-z)=sigma(z)-z`. In every group,
the total coefficient of the common ReLU is exactly zero. The negative
orientations leave explicit linear contributions. Adding those to all
fixed-sign contributions leaves precisely the coefficient vector of
`x_pi(0)`. Thus the network equals the maximum everywhere in the open
cone. All 120 cones pass, and continuity gives equality on their
boundaries as well. The check takes about 0.25 seconds.

This verification is independent of the producer's test: the producer
uses feature values and curvature equations on cone generators, whereas
the checker reconstructs input gradients from the actual network and
checks the resulting linear identity coefficientwise. A known (10,6)
network passes as a positive control; deliberate changes to an output
coefficient, the carrier encoding, and an input dimension are rejected.
This is an exact rational global certificate, not a Lean proof.

Reproduce it with:

    python3 overnight_fixed_cross_verify.py overnight_fixed_cross_net9_17.json
    python3 overnight_fixed_cross_controls.py

## Discovery and current search

All primitive outer coefficient vectors in `[-2,2]^7`, up to overall
sign, form a finite dictionary of 37,969 elements. A numerical linear
solve suggested that two of four path orientations could represent the
target. That residual alone was not a construction certificate.
Restricting to 2,000 promising columns and solving sparse linear programs
gave exact rational candidates, including the fifteen free outer terms
used here. They were checked globally before being recorded as results.

An earlier (9,18) candidate is retained separately. The older general
activation-cone checker was expensive on that candidate; the new exact
global cone argument above is sufficient on its own. The live objective
is a substantially smaller second hidden layer, ideally width six, or
a proof showing why this first hidden layer needs a larger width.
Failed bounded dictionary and sparsification searches imply no
unrestricted lower bound.
