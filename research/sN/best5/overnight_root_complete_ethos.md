# A certified obstruction to retaining the known negative core

25 October 2026. This is a restricted construction obstruction, not a
three-core lower bound for the complete comparison span.

Let V be the span of linear functions and all sigma(x_i-x_j), i<j, on
five inputs. Define

    H_b(a,c) = 2 max(a,c) - max(a,b) - max(b,c),
    g_star(x) = (H_(x1)(x3,x4) - H_(x1)(x0,x2))/2.

This is exactly the negative preactivation of the known (10,6) network
`netB_10_6.json`. There is no identity

    max5 = R + sigma(f1) + sigma(f2) - sigma(lambda*g_star),
    R,f1,f2 in V, lambda>0,

with arbitrary real coefficients. Allowing the opposite sign of g_star
does not change the statement, because sigma(-g)=sigma(g)-g and the
difference is absorbed into R. Permuting all input labels also preserves
the exclusion. No hypothesis fixes either positive preactivation or the
shallow remainder to its value in the old construction.

The geometric bridge is the reviewed mixed-chamber theorem in
`overnight_fixed_complete_uniform_mixed.md`. With three core neurons,
every cancellation inside a braid chamber must be between two equal or
opposite normalized preactivations of opposite output signs; the third
has a weak fixed sign. Boolean quadratic interpolation eliminates R.
The resulting finite QF_LRA formula has unrestricted real parameters,
includes every weak/zero boundary, and includes lambda>0. The complete
model and its scope are described in `overnight_fixed_complete_status.md`.
Non-invariant preactivations can first be removed by the common-translation
limit; this cannot increase the number of invariant cores.

The exact formula is
`overnight_fixed_complete_fixednegative_p2.smt2`. Z3 rejected it, and an
independent cvc5 run produced a CPC refutation. The separate Ethos checker
verified that proof against the original formula and required its last
step to prove false. Its output was `correct`. There are no trust-rule
steps in the saved proof. Thus this is more than agreement between solver
verdicts. The mathematical encoding bridge is a written proof; neither
it nor this network exclusion is a new public Lean theorem.

Reproduce without either solver:

    python3 research/sN/best5/overnight_root_complete_ethos_verify.py

The standard-library replay script checks the source/proof hashes, obtains
the pinned Ethos 0.2.5 Linux x86_64 checker and cvc5-1.4.2 CPC signatures
from their official repositories, verifies all downloaded hashes, and
runs the reference check. Downloads are cached outside the repository.
The manifest contains every dependency hash and URL. The only syntactic
normalizations remove neutral unary operators emitted by Z3 and the outer
API list around cvc5's proof command sequence; no assertion or proof step
is removed. In particular the replay does not normalize integer proof-rule
indices into rational literals.

The full three-core problem remains open: bounded runs of both solvers
timed out on both unrestricted output-sign classes. A new (16,5)
construction would have to change the negative-core shape in the
(+,+,-) case. This obstruction stays in research notes under the user's
requirement that small-input paper results match a construction and bound.
