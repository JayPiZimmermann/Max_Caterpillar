# Exact normalization of arbitrary affine-skip MAX networks

The new public leaf `AffineSkipNormalization.lean` imports the unchanged
nine-array `AffineSkipExtension.AffineSkipNetwork`. Its main theorem is
`AffineSkipExtension.exists_normalizedModel`.

For every positive arity, arbitrary real weights/biases and arbitrary affine
input/output skips, an all-real-input MAX equation yields an explicit
`NormalizedNetwork N h1 h2` computing the same MAX on all real inputs.
Both original finite hidden-layer index types are retained. The new first
row is exactly the original row when its original bias and coordinate sum
both vanish, and is zero otherwise. Every normalized feeding first index
has a nonzero original first-to-second coefficient. No restriction on
output-only first terms, first width, second width, coefficient arithmetic,
or support is assumed.

The proof encodes the nine affine arrays in a homogeneous model with one
extra **input** constant coordinate. This adds no neurons. The existing
exact small-step directional identity at its unit vector yields the
homogeneous network on the original input coordinates, since MAX is
positively homogeneous. The all-ones directional model retains exactly
zero-sum first forms. The existing outer normalization restores zero-sum
second linear skips and unit linear-output slope from the all-real MAX
identity itself.

The independent driver expands both evaluators and all normalization
conditions instead of relying on names. It includes a biased affine-skip
witness and an actual nonlinear MAX3 network at unchanged widths (4,3).
The scoped gate checks the complete current project-source import closure,
forbidden constructs, exact expected types, and eleven standard-only
transitive axiom audits. It does not change any existing normalization leaf.

Reproduce:

    python3 research/sN/jensen_bound/affine_skip_normalization_recheck.py --run
