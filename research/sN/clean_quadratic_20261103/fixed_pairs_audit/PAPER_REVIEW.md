# Review of the assembled quadratic-width draft

Reviewer: `/root/clean_fixed_pairs_audit`, 3 November 2026.

Reviewed artifacts:

* `paper/drafts/quadratic_width/main.tex`
* `paper/drafts/quadratic_width/normalization.tex`
* `paper/drafts/quadratic_width/fixed_pairs.tex`

## Verdict

The assembled argument is mathematically sound relative to the explicitly
stated, previously proved five-input obstruction. Its proof-status notice
correctly says that the document is not yet a self-contained replacement:
the structural certificate is not proved in the document, and the new
fixed-pair argument is not yet formalized in Lean.

The residual model-accounting sentence identified during review has been
corrected and reread. The analytic section is approved in its corrected
state. The whole document remains a working draft because of the displayed
structural-proof residual.

## Wording correction completed

In the event-cover paragraph, the sentence saying that an original outer
neuron with nonzero base preactivation "localizes to a linear or zero term"
is too strong. A positive gate contributes the directional derivative of
its inner function, which can include shallow first-layer ReLUs.

The corrected manuscript now says:

> An original second neuron with nonzero preactivation at the base point
> contributes only linear and shallow first-layer terms, or zero, and
> hence supplies no retained outer ReLU.

The corrected clause was checked directly in the assembled source. It
preserves the existing argument:
the local structural lemma allows arbitrary shallow braid terms, while
its matching witness belongs to an actual retained outer slot.

## Model and scope checks

1. **The public architecture is ordinary.** The displayed network has
   only input-to-first, first-to-second, and second-to-output connections.
   Both hidden biases and the output bias are arbitrary real parameters.
   Exactness is required on all of R^N.

2. **Bias removal is valid pointwise on every real input.** For each fixed
   x, divide F(tx) by t and let t tend to positive infinity. ReLU continuity
   and positive homogeneity remove every bias without changing either
   width. No uniform convergence assertion is needed.

3. **The normalized class retains every required term.** It has an output
   linear head L, shallow terms B_j relu(A_j x), and at most the original
   number of outer ReLUs. A_j and inner heads U_k annihilate the diagonal;
   L has diagonal slope one. This agrees with the exact Lean
   `NormalizedNetwork` and `TranslationNormalized` definitions.

4. **Directional localization gives an all-input representation.** The
   directional derivative identity is obtained for each arbitrary direction
   y, with fixed coefficients determined by signs at the base point. The
   identity therefore holds for every y, even though the sufficiently
   small epsilon used to compute it can depend on y. The proof does not
   mistake agreement in one neighborhood for a global network identity.

5. **The anchor lift preserves translation normalization.** Its identity
   H_S 1_S=1_N shows that every absorbed first-row linear form A_j H_S
   and every inner head U_k H_S still has zero diagonal value. The output
   head L H_S retains value one. The maximum identity holds for every
   positive epsilon because each outside coordinate remains strictly
   below the selected anchor coordinate.

6. **Original widths and interaction graphs are respected.** Positive
   outer derivatives are absorbed into output linear/shallow terms;
   negative ones vanish. Neither operation creates an outer neuron.
   On retained original outer slots, the nonlinear first-row coefficients
   are unchanged. Only first rows wholly supported on the selected set
   remain nonlinear. Thus the interaction graph is exactly the induced
   graph G_k[S], including cancellation of signed parallel contributions.

7. **The structural lemma has the necessary scope.** Its statement uses
   the full normalized representation, including shallow output. This
   matches the actual Lean `LocalMatchingObstruction 5 2` premise. Linear
   heads and shallow terms do not supply uncounted outer matching witnesses.

## Quantifier and counting checks

The public conclusion is

    for every C>0, there exists c_C>0, for every N>=3, ...

The regularization constant B and counting constant D are absolute. The
choice of small delta depends only on their absolute values. With C fixed,
the remaining error terms vanish for all n beyond a threshold depending
only on C, not on the network parameters. Consequently c_C can be chosen
uniformly over all networks and dimensions for that fixed C.

The final finite-range argument is valid: an ordinary network with h2=0
is constant, so every exact MAX_N network has h2>=1. Decreasing c_C handles
the finitely many remaining dimensions. This argument establishes the
displayed fixed-C existential theorem; it does not by itself preserve the
stronger uniform 1/max(1,C) dependence of the separate explicit Lean bound.

The fixed-pair sampling, common large scale, signed activation invariance,
disjoint flip columns, conditional matching law, and O(J^-2) per-neuron
bound were independently checked in `AUDIT.md`. The choice of a common
scale may depend on the finite network, but none of the probability
estimates does. There is no quantifier leak from that choice.

## Verification-status checks

The ordinary theorem receipt and anchor-localization receipt both report
PASS with only `propext`, `Classical.choice`, and `Quot.sound`. The ordinary
existential declarations explicitly reuse the previous explicit proof.
The manuscript states this, and does not claim that those declarations
certify the new fixed-pair proof.

The unproved-in-this-document structural lemma is conspicuously identified
at the beginning and at its statement. The assembled document should remain
a working proof draft until that residual is supplied; it is not yet the
self-contained paper proof requested by the user.
