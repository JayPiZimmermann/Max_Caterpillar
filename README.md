# A caterpillar construction for MAX with two hidden layers

This repository formalizes in Lean 4 an explicit two-hidden-layer ReLU
representation, with rational weights and zero biases, of

$$
\operatorname{MAX}_N(x)=\max_{0\le i<N}x_i
$$

for every positive arity. It also formalizes the Wang–Sun representation of continuous piecewise
affine functions by maxima and the resulting two-hidden-layer networks for
all such functions.

The network model is the ordinary
affine/ReLU/affine/ReLU/affine architecture with real weights, scalar output,
no skip connections, and equality on all of $\mathbb R^N$. For $N\ge3$, define

$$
C_N=\sum_{m=2}^{N-1}\binom Nm\frac{m!}{2}(N-m)m^{N-m-1}.
$$

The construction has widths

$$
h_1=\binom N2+N+1,
\qquad
h_2=3^{N-2}C_N-N(N-1)+2.
$$

Lean proves the displayed widths, including all face corrections, hinge
absorption, and the two signed-remainder units. It also proves
$h_1=O(N^2)$ and $h_2=2^{O(N\log N)}$, with the latter formalized as
$\log h_2=O(N\log N)$. The construction data are given by a direct finite
formula at every arity; its correctness proof uses induction.

## Version 2 results

Superseded declarations are kept in the sources and commented as Version 1;
the new ones are commented as Version 2.

- `maximum_width_rational` (Version 2 of `maximum_width`): the same widths
  with rational weights and zero biases. The canonical inverse-Gram
  coefficients are rational (`coefficient_rational`, `network_rational`).
- `rational_coefficients`: rational coefficients from one basis of the
  dictionary, by an integration-free evaluation argument
  ([Rationality.lean](MaxCaterpillar/Rationality.lean)).
- `compilation`: any expansion of the maximum by normalized face functions
  `K` and an auxiliary remainder compiles with the same first hidden layer and
  `|K| + 2` second-layer neurons ([Compilation.lean](MaxCaterpillar/Compilation.lean)).
- `quotient_compression`: second width `q_N + 2`, where
  `q_N = dim(V_N / A_N)` ([Quotient.lean](MaxCaterpillar/Quotient.lean)).
- `factorial_le_quotientDim`: `q_N ≥ (N - 2)!`
  ([LowerBound.lean](MaxCaterpillar/LowerBound.lean)). This bounds the
  vocabulary dimension only, not the sparsest expansion or general networks.
- `max_three_network`, `max_four_network`: widths `(7, 3)` and `(11, 5)`
  ([SmallArity.lean](MaxCaterpillar/SmallArity.lean)).
- `wang_sun`, `cpwl_two_hidden_layers`, `cpwl_two_hidden_layers_shared`:
  the Wang–Sun theorem and two-hidden-layer networks for all CPWL functions,
  sharing layers across the maxima ([CPWL.lean](MaxCaterpillar/CPWL.lean),
  [Sharing.lean](MaxCaterpillar/Sharing.lean)). The general CPWL development
  under `MaxNN/CPWL` was restored for this purpose.

Exact small-arity searches (`scripts/vocabulary_search.py`) certify
`q_3 = 1`, `q_4 = 65`, `q_5 = 1136`, `s_3 = 1`, `s_4 = 3`; these are
computational certificates, not Lean proofs.

The paper-facing interface begins with
[Definitions.lean](MaxCaterpillar/Definitions.lean),
[Lemmas.lean](MaxCaterpillar/Lemmas.lean), and
[Theorems.lean](MaxCaterpillar/Theorems.lean). The main theorem states:

```lean
theorem maximum_width (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      ∀ x, net.eval x = Maximum N x
```

`Network N h₁ h₂` contains the six real parameter arrays of the two-hidden-layer
network, and `Network.eval` is its explicit nested-sum evaluator.
[Construction.lean](MaxCaterpillar/Construction.lean) defines the compiled
caterpillar network. `network` is the construction used for the stated width
bound.

The proof follows the paper: a signed caterpillar sum is compared with the
support function of a simplex, facet differences reduce the class identity to
one lower-arity case, exposed faces provide the correction dictionary, and the
normalized caterpillar descriptions are compiled into the two hidden layers.
The underlying geometric construction and its relation to the work of
Brunck, Stade, and Yehudayoff are stated in the paper.

## Verification

Lean 4.4.0 and the mathlib revision are pinned in `lean-toolchain` and
`lake-manifest.json`. To reproduce the complete check, run:

```sh
lake exe cache get
ulimit -s unlimited
python3 scripts/verify.py
```

The verifier builds the retained dependency closure, checks the exact public
theorem types, rejects proof holes and new project axioms, and reruns
`#print axioms`. See [verification/BUILD.md](verification/BUILD.md) for the
status of the fresh Max-only verification.

## Paper

The short paper is [paper/main.tex](paper/main.tex). Build instructions and
Lean-link conventions are in [paper/README.md](paper/README.md). The repository
is hosted at
[JayPiZimmermann/Max_Caterpillar](https://github.com/JayPiZimmermann/Max_Caterpillar).
