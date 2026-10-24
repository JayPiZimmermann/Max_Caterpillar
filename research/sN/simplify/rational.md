# Rational weights and zero biases of the Caterpillar Net: a short proof

## Lemma (rationalizing an expansion)

Let g_1, ..., g_m, f : R^N -> R be continuous, rational-valued on Q^N, and
suppose f = sum_i c_i g_i with real c_i. Then f = sum_i c'_i g_i with c'_i in Q.

*Proof.* Regard R as a vector space over Q and let pi : R -> Q be a Q-linear map
with pi(q) = q for q in Q (extend {1} to a Q-basis of R and take the coordinate
of 1). Put c'_i := pi(c_i). For y in Q^N the numbers g_i(y) and f(y) are
rational, so Q-linearity of pi gives

    f(y) = pi(f(y)) = pi( sum_i g_i(y) c_i ) = sum_i g_i(y) pi(c_i) = sum_i c'_i g_i(y).

Both sides are continuous and agree on the dense set Q^N, so they agree on R^N. ∎

## Application (replaces the second paragraph of the proof of thm:quotient-compression)

Suggested paper text (to replace "The coordinates are rational. ... \in\mathbb Q." incl. eq:rational-coordinate):

> The coefficients can be taken rational. Every \(g_i\) and \(\maxn_N\) is
> continuous and takes rational values on \(\mathbb Q^N\), being built from
> \(\relu\) and integer combinations of coordinates. Let
> \(\pi\colon\mathbb R\to\mathbb Q\) be \(\mathbb Q\)-linear with \(\pi(q)=q\)
> for \(q\in\mathbb Q\). For \(y\in\mathbb Q^N\), applying \(\pi\) to
> \(\maxn_N(y)=\sum_i g_i(y)\,c_i\) gives
> \(\maxn_N(y)=\sum_i\pi(c_i)\,g_i(y)\). Both sides are continuous and agree on the
> dense set \(\mathbb Q^N\), so \(\maxn_N=\sum_i\pi(c_i)g_i\) on \(\mathbb R^N\),
> with the same support \(K\).

(Since the lemma accepts *any* real expansion, the words "with unique real
coordinates" in the preceding sentence become unnecessary; uniqueness/basis is
still used for the count |K| <= q_N, not for rationality.)

Rest of the argument (unchanged, already short):
* First hidden layer: weights are the rows of x_i, -x_i, x_i - x_j: integers.
* Second hidden layer: heads h_k and labels ell are integer combinations of
  e_i - e_j (normalized descriptions), so integer weights; the extra two
  neurons carry the auxiliary remainder with the rational coefficients a_j.
* Output layer: the coefficients d_k, a_j: rational by the lemma.
* Zero biases: every unit and auxiliary function is positively homogeneous
  and linear in x without constant term, so the compilation uses no biases.

## Self-check

1. Existence of pi: needs a Q-basis of R containing 1 (axiom of choice); Lean:
   `LinearMap.exists_leftInverse_of_injective` applied to the inclusion
   `Algebra.linearMap ℚ ℝ`. A choice-free alternative: the system
   sum_i c_i g_i(y) = f(y), y in Q^N, has rational coefficients; a finite
   subsystem has the same row space, and a rational linear system with a real
   solution has a rational one (Gaussian elimination). Not needed in Lean.
2. Q-linearity is used only on products g_i(y) c_i with g_i(y) in Q: correct,
   pi(q c) = q pi(c).
3. pi(f(y)) = f(y) needs f(y) in Q: max of rational coordinates is rational.
4. Rational values of U_k on Q^N: relu and integer combinations preserve Q.
5. Continuity: all functions are finite compositions of relu and linear maps.
6. The support K is untouched (only the coefficients change), so the width
   |K| + 2 and the bound |K| <= q_N are unaffected.
7. No independence/basis is needed for rationality, and no evaluation points
   are chosen explicitly.
Lean-verified: `exists_rat_coeff_of_mem_span_v4` and `caterpillar_net_v4`
(MaxCaterpillar/Simplify/Rational.lean), axioms propext, Classical.choice,
Quot.sound; `caterpillar_net_v4` has type identical (rfl) to `caterpillar_net`.

## Lean comparison

| part | old (lines) | new (lines) |
|---|---|---|
| generic coefficient lemma | Rationality.lean `rows_span_top` .. `exists_rat_coeff_of_mem_span` (sections Rows/Points/Span, l. 68-250): 183 | `exists_rat_coeff_of_mem_span_v4`: 31 |
| assembly for N >= 3 | `quotient_compression` (130) + `quotientDim_eq` (7) + `quotientDim_le_essential` (18) + `quotientDim_add_two_le_secondWidth` (12) + `maximum_width_one_basis` (15) = 182 | `caterpillar_net_v4`: 44 |
| total | ~365 | 75 (file 97 incl. header) |

The new assembly does not pass through q_N: it uses K = essential normalized
descriptions directly (max_N in span(essential units) + A_N by
`vocabularySpan_le_essential`), whose size already gives |K| + 2 <= secondWidth.
`quotient_compression` (the sharper width q_N + 2) is still needed for
thm:quotient-compression itself; there, the rationality step can switch to the
v4 lemma by replacing one identifier (`exists_rat_coeff_of_mem_span` ->
`exists_rat_coeff_of_mem_span_v4`; the v4 lemma is strictly more general — it
drops the `[DecidableEq ι]` hypothesis), which would make the 183 lines of
Rationality.lean l. 68-250 unnecessary. Existing files are not modified.
Reused unchanged: `ratField`, `ratPoints`, `eq_of_eq_on_ratPoints`
(Rationality.lean l. 1-66), the ratField value lemmas of RationalWidth.lean,
`compile_expansion_width`, and the N = 1, 2 cases.
