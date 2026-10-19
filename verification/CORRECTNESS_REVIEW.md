# Correctness review of the Max caterpillar manuscript

Date: 2026-10-19. Status: **all listed manuscript repairs implemented and independently source-reviewed**.

Four independent subagents reviewed (1) face corrections and dictionary membership, (2) simplex reconstruction and facet grouping, (3) the arity induction, and (4) canonical coefficients, network compilation, and widths. Their source reviews were compared with the retained Lean proofs. The parent agent separately ran the complete Lean verification.

**No reviewer found a counterexample, a false width bound, or a circular dependency in the checked Lean proof.** The original review found several incomplete manuscript justifications and two paper-to-Lean correspondence issues. Those findings are retained below as a historical record; the current working manuscript contains the repairs summarized in the resolution table. Independent follow-up source reviews cleared the repaired face-correction, full-dimensionality, Gram, dictionary, reconstruction, arity-induction, coefficient, width, coordinate-deletion, and rooted-star arguments, including the relevant indices and signs.

## Reviewed snapshot and verification

- Manuscript: [paper/main.tex at the reviewed root commit](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex), SHA-256: 73b47f4459a35a3c2637c916f8750fd4e51d265b851955ae3b99700ef4ed4f32.
- Lean source digest from the [historical certificate](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/verification/certificate.json): 16eae06d5f72bd2b0b0353597a5b3c164b2cf77e1b4993d4398f8d0d0679f8e9.
- The complete gate passed: **27 exact theorem statements, 166 Lean files**, including the Lake configuration. The permitted axioms were only `propext`, `Classical.choice`, and `Quot.sound`.
- The gate built All and Verification.Statements, re-elaborated the stated types, checked their axiom dependencies, and scanned project Lean sources for sorry, admit, new axiom declarations, and native_decide.
- Paper checks passed: 13 pages, 98 Lean hyperlinks, 85 linked equations (83 Lean and 2 literature links), and no overfull boxes.
- The reviewers performed source inspection; the build result is the parent's separate verification. Neither constitutes a new audit of Lean's kernel or Mathlib.

A fresh full gate on the current tree again passed all 27 exact statements and all 166 Lean files. The current certificate has SHA-256 `7ad1e4d547633aca3e08023e32bff3399a8536ca394f7a548f773cdd2f213639` and aggregate source digest `5309e0d5ace2238c88342f271dff6092ab51c265977ae6d741ae91cae0e349ad`; all 169 recorded source and manifest hashes match the current files. The mathematical declarations are unchanged from the reviewed proof; the intervening Lean edit changed only a three-line explanatory comment.

The snapshot hashes and build counts above are historical and remain unchanged. Paper line references in the original findings pin root commit [`3295f962bfa66108d570048962457c89c5112926`](https://github.com/JayPiZimmermann/Max_Caterpillar/tree/3295f962bfa66108d570048962457c89c5112926), so they continue to identify the manuscript that was reviewed.

## Resolution status in the current manuscript

Here, “implemented” means that the stated repair is present in `paper/main.tex`. The evidence column records a completed source comparison with the named Lean declarations; it does not claim that the prose itself is machine checked. The mathematical declarations used by the review remain unchanged, and the current tree passed a fresh full Lean gate after the comment-only edit described above. PDF-build evidence is recorded separately in `verification/paper.json`; this review does not assert a fresh paper build.

| Item | Status and current manuscript location | Lean source used for comparison |
| --- | --- | --- |
| Main 1: tagged coefficients | Implemented. The tag map, equal fiber split, literal tagged expansion, and normalization-fiber aggregation are explicit in `eq:tag-family`, `eq:tagged-coefficients`, `eq:tagged-expansion`, and `eq:normalized-tag-coefficients`. | `Canonical.taggedCoeff`, `Canonical.sum_taggedCoeff_eq`, and `CorrectionTable.normalizedCoeff` |
| Main 2: coordinate-deletion fibers | Implemented. `eq:coordinate-active` classifies the surviving terms; `eq:coordinate-fibre-partition` gives the inverse insertion/deletion rules; `eq:insertion-weight-germs` gives their weights and signs. | `coordinateUpperTerm_sub_active_mem_LSpan`, `coordinateFibreEquiv`, and `coordinateStructuredBlock_sub_lower_mem_LSpan_one` |
| Main 3: two-value cancellation | Implemented. The active domain, preservation, involutivity, sign reversal, inactive cases, and resulting facet-difference comparison are stated around `eq:block-pairing`. | `blockTransform_involutive` and `germDiff_formula_mem_LSpan_of_repeatedValues` |
| Main 4: empty-cut stars | Implemented. The linear apex term and singleton state are identified before `eq:root-star`; `eq:boolean-cancellation` and `eq:root-star-average` connect the fixed-root identity to the weighted permutation sum. | `emptyCut_coordinateLowerUnit_sum_mem_LSpan` and `coordinateEndpointStarSum_mem_LSpan` |
| Main 5: pyramid dimension | Implemented after `eq:unit-polytope`: the head and edge functions are jointly independent because their label edges form a tree on all labels, proving both full dimension and that the apex is outside the base affine hull. | `fullDimensionalWords` |
| Main 6: Gram positivity | Implemented after `eq:inner-product`: continuity turns zero squared integral into vanishing on the cube, positive homogeneity extends this to all inputs, and basis independence gives positive definiteness. | `gramMatrix_isUnit` and `atomFunction_posHomContinuous` |
| Main 7: dictionary link | Implemented. Definition `def:dictionary` links to `MaxCaterpillar.dictionary`; `eq:aux_functions` separately links to `featureLayer`. | `MaxCaterpillar.dictionary` and `featureLayer` |
| Main 8: reconstruction residual | Implemented. `eq:ridge-cut-residual` displays the exact cut residual, while `eq:single-facet-group` and `eq:facet-group-bound` compare each signed group with `D_u f`. | `residual_ridgeCut` and `germDiff_hS_simplex_sub_mem_LSpan` |
| Small 1: zero direction | Implemented in the dimension-reduction paragraph: the proof fixes `u\ne0` only after stating `D_0f=0`; the operator itself remains defined for every direction in `eq:facet-difference`. | `germDiff_hS` and the definition `germDiff` |
| Small 2: base-face hinge orientation | Implemented in Step `stp:corrections`, which explicitly invokes `eq:hinge-reversal` before placing both hinge orientations in the auxiliary span. | `hS_coord_mem_realUnitSpan_of_mem_coneFamily` |
| Small 3: the `N(N-1)` subtraction | Implemented before `eq:normalized-tag-coefficients`: the manuscript proves that ordered coordinate-difference heads and their ReLUs are distinct before forming the absorbable subset; `eq:retained-count` then performs the subtraction. | `orderedHingeKey_injective` and `essentialNormalizedKeys_card_le_sub_orderedHinges` |
| Small 4: small arities | Implemented after the proof of Theorem `thm:main`: the text separates the `N\ge3` construction from the `N=1,2` base networks. | `maximum_width` and `construction_width` |
| Small 5: direction classification | Implemented in `eq:direction-pattern` and its surrounding exhaustion argument before the cancellation cases. | `block_or_braid_of_unique_edge_tie` and `germDiff_coordinateResidual_mem_LSpan_of_canonical` |
| Small 6: three-value reflection | Implemented in `eq:braid-reflection`, `eq:braid-germ`, and `eq:linear-facet`, including `R u=-u`, the linear covariance term, and the derivative conclusion. | `germDiff_formula_smul_braid_mem_LSpan_zero` |
| Small 7: translated coordinate | Implemented in `eq:lower-arity-translation`; the correction `(W_{N-1}-1)x_1` is explicit, and `eq:lifted-induction` states the exact induction consequence. | `valueFormula_sub_MAX_eq` and `valueFormula_sub_MAX_mem_LSpan` |

The final network presentation was also independently source-reviewed: the remainder is defined from auxiliary and absorbed coefficients, its compact readout uses the positive-shift identity, and the first-layer feature order, second-layer rows, output weights, and zero biases agree with the Lean compiler up to the fixed index enumerations. The final manuscript SHA-256 is `dd999ce9ba91487c8d489f7bc6752d4f9dca2190727d540c39262126abb24e0e`. The rebuilt PDF and link/layout checks are recorded in [paper.json](paper.json).

The conclusion also reports the separately formalized results `MaxNN.QuadCover.twoHidden_firstWidth_quadThreshold` and `MaxNN.QuadCover.twoHidden_pairHinge_firstWidth`. Their source-bound QuadCover verification receipt in the research repository records a full rebuild and kernel replay with only the standard foundational axioms. The first extends Lu’s numerical bound to arbitrary affine skip connections; the second improves the bound under the explicit pair-direction hypothesis. They are not part of this repository’s 27-claim construction audit, and the manuscript identifies that development as separate.

## Historical findings requiring attention

### 1. The paper omits the bridge from function coefficients to the actual tagged Lean network

**Priority: medium. Type: construction correspondence.**

At [main.tex:243](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L243), the dictionary is a set of distinct functions. The coefficient rule assigns a coefficient $c_g$ to each such function, and [main.tex:667](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L667) compiles these coefficients using a set of retained functions. This gives a valid existence argument after choosing a description for each function. It does not specify the same coefficient bookkeeping as the named Lean network.

Lean first uses a finite family of tags, including face descriptions and auxiliary-feature indices. It takes distinct functions when forming inverse-Gram bases and divides each function coefficient equally among all tags representing that function. It then sums the coefficients of raw face-description tags along fibers of the normalization map; auxiliary-feature tags keep their shares in the remainder. Distinct normalized descriptions can still represent the same function.

**Repair:** explicitly introduce the tag map $v:A\to\mathcal D$, set

$$
\widetilde c_i=\frac{c_{v(i)}}{|\{j\in A:v(j)=v(i)\}|},
$$

and explain that normalization adds these coefficients over raw face-description tags with equal normalized descriptions. Keep the auxiliary-feature shares in the remainder, and count retained descriptions when describing the actual Lean network. Alternatively, give a representative-selection rule for the paper's network and clearly distinguish it from the named Lean construction.

Evidence: [Canonical/Coefficients.lean:83](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Coefficients.lean#L83), [Canonical/Table.lean:90](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Table.lean#L90), [Canonical/Table.lean:159](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Table.lean#L159), and [Construction.lean:71](../MaxCaterpillar/Construction.lean#L71).

**Assessment:** no error in the asserted existence or width bound was found. The omitted bridge matters for the stronger claim that the displayed recipe specifies the formalized network.

### 2. The coordinate-deletion count lacks an exhaustive classification of contributing terms

**Priority: medium. Type: missing proof step.**

[main.tex:597](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L597) says to delete label $0$ from each “contributing caterpillar” and counts $N-2$ pendant insertions and two spine-end insertions. The paragraph does not characterize contributing terms or establish that these insertion families are disjoint and exhaust the terms remaining modulo $\mathcal L_{N-3}$.

**Repair:** state the criterion for a term to survive, identify the two endpoint cases and the pendant cases, and explain why deletion and insertion are inverse on each case. Then the count $N$ and the factor $1/N$ follow. Keep the separate empty-cut exception explicit.

Evidence: coordinateUpperTerm_sub_active_mem_LSpan in [Coordinate/Active.lean:44](../MaxNN/Constructions/Paramid/Caterpillar/Coordinate/Active.lean#L44), coordinateFibreEquiv in [Coordinate/ReindexActive.lean:228](../MaxNN/Constructions/Paramid/Caterpillar/Coordinate/ReindexActive.lean#L228), and [Coordinate/Structured.lean:67](../MaxNN/Constructions/Paramid/Caterpillar/Coordinate/Structured.lean#L67).

**Assessment:** the insertion count and signs were checked against Lean and are correct. The reviewed snapshot omitted the bijection needed to justify them.

### 3. The two-value cancellation asserts a pairing without proving its domain and involution properties

**Priority: medium. Type: missing proof step.**

[main.tex:580](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L580) describes toggling a cut, sometimes together with exchanging adjacent labels. It does not explain why every term needing cancellation has the stated block form, why the transformation stays within the relevant cases, or why it is involutive on the active pairing cases. Its inactive fixed points must be handled separately by the preceding dimension bound.

**Repair:** identify the remaining active terms first; then state preservation, involutivity, reversal of the coefficient sign, and equality of facet differences modulo $\mathcal L_1$. Terms outside that domain must be accounted for by the preceding dimension bound.

Evidence: blockTransform_involutive and the sign lemmas in [Block/Transform.lean:194](../MaxNN/Constructions/Paramid/Caterpillar/Block/Transform.lean#L194); the complete cancellation is [Block/Global.lean:62](../MaxNN/Constructions/Paramid/Caterpillar/Block/Global.lean#L62).

**Assessment:** the formal cancellation is complete; the manuscript's explanation is too compressed to establish it on its own.

### 4. The empty-cut star argument skips the connection between the actual residual and the Boolean identity

**Priority: medium. Type: missing identification.**

At [main.tex:599](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L599), the extra terms are identified with rooted stars, followed by the Boolean identity for $T_A$. [main.tex:611](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L611) then concludes by “averaging over the possible apex labels.” The actual empty-cut lower unit includes a linear apex term as well as a singleton-state function. The paragraph does not exhibit this decomposition or the correspondence between summing apex choices at a fixed root and the singleton sum.

**Repair:** at a fixed root, write the lower unit as its linear apex term plus $T_{\{i\}}$. Summing over the possible apex gives the singleton sum, modulo linear functions. Apply the displayed identity there, then sum over roots and permutations with their weights.

Evidence: [Coordinate/Star.lean:111](../MaxNN/Constructions/Paramid/Caterpillar/Coordinate/Star.lean#L111), emptyCut_coordinateLowerUnit_sum_mem_LSpan at [line 315](../MaxNN/Constructions/Paramid/Caterpillar/Coordinate/Star.lean#L315), and the endpoint-star result at [line 345](../MaxNN/Constructions/Paramid/Caterpillar/Coordinate/Star.lean#L345).

**Assessment:** the identity and dimension estimate are valid. The missing link is how they apply to the weighted residual.

### 5. The pyramid conclusion requires independence of the head as well as the edge vectors

**Priority: low to medium. Type: incomplete inference; conclusion true.**

[main.tex:238](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L238) says that the edge vectors are independent, “so” the polytope is a pyramid over a parallelotope. Edge independence proves the parallelotope statement, but does not show that the apex lies outside its affine hull.

**Repair:** state that the head and all $N-2$ edge functions are jointly linearly independent; equivalently, their restrictions form a basis of $H_0^*$. The edges form a tree on the $N-1$ non-apex labels; adjoining the head edge connects the apex, giving a tree on all $N$ labels. This proves dimension $N-1$ and the pyramid property. The unreduced coefficient vectors lie in the sum-zero hyperplane, which should not be confused with the primal space $H_0=\{x_0=0\}$.

Evidence: fullDimensionalWords in [Corrections/FullDim.lean:109](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/FullDim.lean#L109), using simplex_differences_linearIndependent.

### 6. Positive definiteness of the Gram matrix needs the continuity and homogeneity argument

**Priority: medium. Type: omitted justification.**

[main.tex:275](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L275) asserts positive definiteness. Linear independence as functions on all of $\mathbb R^N$ alone would not ensure independence after restriction to the integration cube.

**Repair:** explain that every dictionary function is continuous and positively homogeneous. A linear combination with zero squared integral vanishes on the cube by continuity; positive rescaling then makes it vanish everywhere. Independence of the chosen basis makes its coefficient vector zero.

Evidence: IsPosHomContinuous, the separation argument, and gramMatrix_isUnit in [Canonical/Gram.lean:23](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Gram.lean#L23), [line 58](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Gram.lean#L58), and [line 172](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Gram.lean#L172). The atom hypotheses are established in [Canonical/Table.lean:32](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Canonical/Table.lean#L32).

**Assessment:** invertibility is true and formalized; this is an exposition gap.

### 7. The dictionary definition links to the auxiliary features rather than to the dictionary

**Priority: low. Type: incorrect declaration target.**

The Lean link in the title of the dictionary definition, [main.tex:242](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L242), targets featureLayer. That declaration contains the auxiliary features, not the union with the caterpillar face functions.

**Repair:** link the definition title to MaxCaterpillar.dictionary in [Construction.lean:68](../MaxCaterpillar/Construction.lean#L68). The existing featureLayer link is appropriate for the auxiliary-feature equation.

**Assessment:** the linked declaration is incomplete for the definition it accompanies. This is a traceability error, not a false dictionary theorem.

### 8. Reconstruction needs a more explicit residual identity and facet-group comparison

**Priority: low to medium. Type: compressed proof.**

At [main.tex:525](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L525), the ridge-cut argument refers to a linear combination of section corrections without displaying how they arise. The conclusion beginning at [main.tex:527](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L527) correctly defines the signed facet groups, but the equality modulo $\mathcal L_{N-3}$ between a group and $D_uf$ remains compressed.

**Repair:** display the reconstruction residual under one cut, identifying the section support function and the transformed lower-dimensional terms. For each normalized direction $u$, explicitly write that $D_uf-G_u\in\mathcal L_{N-3}$: linearity accounts for each simplex, and differentiating the subdivision remainder lowers its dimension bound. This directly explains why $G_u\in\mathcal L_{N-3}$.

Evidence: residual_ridgeCut in [Geom/Reconstruct.lean:150](../MaxNN/Constructions/Paramid/Geom/Reconstruct.lean#L150), and germDiff_hS_simplex_sub_mem_LSpan in [Reconstruct/FacetGerm.lean:322](../MaxNN/Constructions/Paramid/Geom/Reconstruct/FacetGerm.lean#L322).

**Assessment:** the reviewer checked the signs, multiplicities, base case, and dimension bounds and found no error. The argument is independent of the later arity induction, so there is no circularity here.

## Historical smaller clarity and traceability issues

1. **Zero direction:** the introduction of facet differences around [main.tex:324](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L324) uses nonzero directions, while later statements quantify over all directions. State $D_0=0$ when introducing $D$, or consistently quantify over nonzero directions. The Lean operator is defined at zero and the proof later handles it correctly.
2. **Base-face hinges:** [main.tex:403](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L403) should mention the hinge-reversal identity when placing negatively oriented edge hinges in the auxiliary span. That identity is already available; [Corrections/Span.lean:118](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/Span.lean#L118) supplies the formal argument.
3. **Subtracting $N(N-1)$:** [main.tex:663](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L663) should explicitly state that the ordered-pair hinge functions are distinct before subtracting their count. [Corrections/HingeCount.lean:109](../MaxNN/Constructions/Paramid/Caterpillar/Corrections/HingeCount.lean#L109) proves the required injectivity.
4. **Small arities:** the paper's main theorem starts at $N\ge3$, while the linked maximum_width theorem covers every positive $N$. This is a stronger valid Lean statement, not a mismatch in the bound. Explain that $N=1,2$ use separate base networks, or additionally link construction_width, which exactly matches the paper's range.
5. **Direction classification links:** the classification used in Step 7.3 is supported by [Geometry/Facets/Pattern.lean:110](../MaxNN/Constructions/Paramid/Caterpillar/Geometry/Facets/Pattern.lean#L110) and [Formula/CoordinateDirections.lean:51](../MaxNN/Constructions/Paramid/Caterpillar/Formula/CoordinateDirections.lean#L51). Links to these would help distinguish the dimension classification from the later cancellation.
6. **Three-value reflection:** [main.tex:573](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L573) could state the two identities $R(u)=-u$ and $F_N\circ R-F_N\in\mathcal L_0$, together with the derivative covariance, to make the claimed linear facet difference easier to follow.
7. **Restoring the translated coordinate:** [main.tex:589](https://github.com/JayPiZimmermann/Max_Caterpillar/blob/3295f962bfa66108d570048962457c89c5112926/paper/main.tex#L589) is correct, but does not display the linear correction. If $W_{N-1}$ is the total signed coefficient sum, the correction is $(W_{N-1}-1)x_1$; there is no need to assume $W_{N-1}=1$. [Formula/Lift.lean:30](../MaxNN/Constructions/Paramid/Caterpillar/Formula/Lift.lean#L30) proves the exact relation. This is the precise use of the arity induction hypothesis.

## Specific points checked without finding a flaw

- **Face corrections:** the vertex-deletion sign $(-1)^{N-|T|+1}$, the outer induction on simplex vertex sets, the inner residual-dimension induction, and the choice of directions avoiding finitely many proper subspaces are consistent. The smaller-simplex induction hypothesis is used for support functions of proper simplex faces created during residual elimination.
- **Facet reconstruction:** the two-facet base case and the two-dimensional quotient in the ridge-cut step are valid. Lean's inward-normal convention and the manuscript's outward-normal convention give the same signed identity after conversion.
- **Arity induction:** the exceptional-direction reduction, insertion signs, $N$-to-one weighted recovery, and lower-dimensional empty-cut correction agree with the formalization. The lifted lower-arity class identity is used exactly in the second bracket of the final error split.
- **Network semantics:** the public network is an affine/ReLU/affine/ReLU/affine map on all of $\mathbb R^N$, with two hidden layers and the stated width parameters.
- **Width bound:** normalization, the leaf-order quotient, fixed-point-free spine reversal, shared first-layer features, absorption of pair hinges, and two remainder neurons support the displayed bound. No arithmetic or asymptotic error was found.
- **Cube versus ball:** an initially raised objection was retracted. Lean's concrete space Fin N → ℝ uses the sup norm, so its closed unit ball is exactly $[-1,1]^N$. The chosen Haar normalization multiplies both the Gram matrix and right-hand side by the same positive constant and therefore leaves $G^{-1}b$ unchanged. There is no domain mismatch.

## Scope of the repository reduction

The verified source tree retains the Max caterpillar construction and its required geometric and network infrastructure. The general CPWL representability proof and archived alternative constructions have been removed. General CPWL results remain cited mathematical background in the introduction; those citations are not claims that their proofs remain formalized in this repository.

The review did not establish historical priority, independence from unpublished work, or equivalence with another group's concurrent proof. It also does not claim optimality of the width bound.

## Historical suggested repair order

1. Restore the tag-to-function coefficient bridge and fix the dictionary link.
2. Supply the active-term classification, insertion bijection, cancellation involution properties, and fixed-root star decomposition.
3. Add the head-independence and Gram-positivity arguments.
4. Clarify the reconstruction residual and facet-group comparison.
5. Address the smaller notation and link issues.

All items in this historical repair order are implemented in the current working manuscript, cross-referenced in the resolution table above, and cleared by the independent follow-up source reviews.
