# Lean-only width audit and a complete CPWL control frontier

This branch uses symbolic Lean proofs only. No numerical experiments or
external solver verdicts support any new claim here. The declarations are
research leaves, not imported by the public root.

## A genuine tradeoff, for a CPWL target other than the maximum

`AuditTent.lean` uses the repository's actual `Network` definition, with
arbitrary real weights and biases, two hidden layers, and no skip connections.
For the one-input function

\[
T(x)=\sigma(x)-2\sigma(x-1)+\sigma(x-2),
\]

`tent_widths_iff` proves the complete equivalence

\[
T\text{ has widths }(a,b)
\quad\Longleftrightarrow\quad
(a\ge1\land b\ge2)\lor(a\ge2\land b\ge1).
\]

Thus the Pareto frontier is exactly `(1,2)` and `(2,1)`. The minimum second
width is two at first width one and one at every first width at least two.
The minimum first width and minimum second width are both one, but no single
network attains both. This refutes a general simultaneous-minimum principle
for CPWL functions. **It does not settle the maximum-function frontier.**

The two constructions are the identities

\[
T(x)=\sigma(2-\sigma(x))-2\sigma(1-\sigma(x)),
\qquad
T(x)=\sigma\bigl(\sigma(x)-2\sigma(x-1)\bigr).
\]

Lean checks them for every real input by exact case splits. A `(1,1)`
network is a composition of scalar affine maps and ReLUs, so is monotone or
antitone. Its values cannot equal the target's values zero, one, zero at
inputs zero, one, two. A zero-width hidden layer gives a constant function.
Padding the two explicit networks proves sufficiency for every larger pair.

The exact-width specializations are `tent_first_one_iff` and
`tent_first_two_iff`. All these declarations and the generic
`network11_mono_or_anti` lemma have only `propext`, `Classical.choice`, and
`Quot.sound` as axioms.

## Existing maximum results audited

`AuditExisting.lean` checks these exact statements in the arbitrary-bias
`Network` model:

- `max3_widths_iff`: precisely first width at least four and second width
  at least three; the least pair is `(4,3)`.
- `max4_widths_iff`: precisely first width at least six and second width
  at least three; the least pair is `(6,3)`.
- `SmallN.Max5General4.max_network`: a rational zero-bias `(16,6)` network
  computing the five-input maximum.
- The old general first-width theorem gives at least six at five inputs.
  The new branch `LowerFirst.lean`, owned by the lower-bound agent,
  strengthens this to seven using the existing monomial rigidity lemma.

The separate existing leaf
`research/sN/frontierN/overnight_general_antipodal.lean` was recompiled.
Its `network_second_width_half_plus_one` proves `N+2 <= 2*h2` for every
positive arity and every exact maximum network, without a first-width
hypothesis and including arbitrary biases. In particular it proves second
width at least four at five inputs. Both its network theorem and homogeneous
theorem passed the axiom audit with the same three standard axioms.

The historical minimum-first-width-nine claim is not a consequence of these
audited declarations. Its finite certificate and written bridge must not be
substituted for a complete Lean theorem under the user's current evidence
requirement. The construction agent has separately proved `(10,6)` in
`UpperMax5.lean` and is formalizing `(9,14)`; consult those modules' final
build and axiom receipts for their status. `audit_review.md` records the
independent review of both physical-width bridges.

## Local verification

```
lake env lean research/sN/width_tradeoff/AuditTent.lean
lake env lean research/sN/width_tradeoff/AuditExisting.lean
lake env lean research/sN/frontierN/overnight_general_antipodal.lean
```

Durable logs: `audit_tent.log`, `audit_existing.log`,
`audit_antipodal.log`. Each final run exits zero and prints the audited axiom
sets. No GitHub build, push, numerical search, or paper edit was performed.
