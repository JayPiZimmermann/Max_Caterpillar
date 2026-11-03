# Jensen PDF: MAX5 width scope

Read-only audit of `notes/paper_simon_jensen.pdf`, 3 November 2026.
PDF SHA256: `bf1e9e86bcad537a66ea1f2c71ac297df405f6a6bcbc10ea78038dc2861c2104`.
Page numbers below are both the printed page numbers and PDF page indices
counted from one. Extraction used `pdftotext -layout`.

## Main finding

The PDF supplies no stronger unrestricted *ordinary no-skip* MAX5 width
result than the repository frontier already records. Its headline
`h2(5)=4` is explicitly for braid first layers in a model with affine
skip connections. It is not a physical four-neuron second hidden layer
construction for the ordinary architecture.

## Relevant passages and their meaning

* Page 1, equation (1): the network model includes input-to-second-layer
  linear heads, input-to-output affine terms, and first-to-output terms.
  Affine skip connections are allowed throughout.
* Pages 4–5, related work: the PDF credits the repository's general
  `ceil(N/2)-1` bound with skips, and its stronger no-skip bounds
  `ceil(N/2)` and later `ceil(N/2)+1`. At N=5 the latter yields physical
  second hidden width at least four. The paragraph also credits
  `Max5General4`: six comparison first neurons, skip connections, four
  correction neurons. It does not assert physical widths (6,4) without
  skips.
* Page 6, Lemma 8: recession deletes biases; localization at the diagonal
  gives a sum of folded shallow functions plus a shallow remainder.
  This does not preserve a no-skip *presentation*: the remainder and
  linear heads are permitted by the ambient model.
* Page 7, Remark 12(d): the localization recursion gives only `h2(5)>=2`
  for the skip model, weaker than the restricted braid statements. Its
  `h2(N)=1` at N=3,4 is likewise a skip-model assertion.
* Page 36, Section 10: the asserted exact braid residual minimum four
  uses a hand lower bound of three, then an SMT exclusion of three
  neurons. The author explicitly says that this is a solver verdict,
  cross-checked by a second solver and encoding, **without a checkable
  certificate**. The underlying proof is referred to supplementary
  `notes/small-widths.md`; the PDF itself does not give its full argument.
  The upper bound is again the repository's `Max5General4` identity.

The later repository certificate package for complete comparison-space
residual minimum four is stronger evidence than the PDF's reported
solver-only exclusion. Neither restricted result excludes an ordinary
physical width-four or width-five network with arbitrary first directions.

## Consequence for the search

Retain the repository's ordinary frontier: minimum first width nine;
known upper pairs (9,11) and (10,6); unrestricted minimum second width in
[4,6]. Do not translate a residual count into a physical count without
accounting for the shallow remainder and its carrier neurons.
