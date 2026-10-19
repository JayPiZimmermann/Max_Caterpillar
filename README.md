# A caterpillar construction for MAX with two hidden layers

This repository formalizes in Lean 4 an explicit two-hidden-layer ReLU
representation of

$$
\operatorname{MAX}_N(x)=\max_{0\le i<N}x_i
$$

for every positive arity. The formalization in this repository is restricted
to this maximum construction and the mathematics used in the accompanying
paper. It does not contain a formalization of the general theorem for arbitrary
continuous piecewise affine functions.

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
caterpillar network. `network` is the construction used for the closed width
bound.

The proof follows the paper: a signed caterpillar sum is compared with the
support function of a simplex, facet differences reduce the class identity to
one lower-arity case, exposed faces provide the correction dictionary, and the
normalized caterpillar descriptions are compiled into the two network layers.
The underlying geometric construction and its relation to the work of
Brunck, Stade, and Yehudayoff are stated in the paper and in
[PROVENANCE.md](PROVENANCE.md).

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
