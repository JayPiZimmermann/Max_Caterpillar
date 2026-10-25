# The canonical-star flag separator does not extend to arbitrary heads

25 October 2026. This closes one proposed extension of an existing separator;
it is not a nonexistence result for general-head star constructions.

Use the six complete flags and weights in
`dfs_review_flag_certificate.log`, symmetrized over all 120 label permutations.
Their value on the five-vertex simplex is 120 and their value on every
canonical rooted oriented star is zero.

For apex label 0, centre 1 and leaves 2,3,4, instead take the unit

```
sigma(-x0 + 6*x1 - 3*x2 - 2*x3
      + sigma(x2-x1) + sigma(x3-x1) + sigma(x4-x1)).
```

The same symmetrized flag functional has value **-6** on its support
polytope. Thus merely allowing arbitrary linear heads already invalidates
the extension. Positive unequal segment lengths give further counterexamples.

`overnight_root_star_flags.py` computes the values directly from vertex maxima
and minima, without a Fourier model. Its controls include all 32 root and edge
orientation choices on a fixed labelled star; symmetrization covers every
other labelling. The receipt records the three explicit counterexamples.
