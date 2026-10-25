# Independent review of the dictionary-proof simplification

Reviewer: the independent dimension-proof agent. Verdict: **PASS** for the
mathematical arguments and the Lean definitions/quantification reviewed below.
This is a read-only semantic review; build and axiom verification belong to
the author/root's separate receipts.

## Paper: finite elimination

The subspace `V = span D` is closed under the face derivative: caterpillar
face supports stay within the family under another exposed face, while
coordinate/difference segment supports and linear forms stay in the same span.
The sign `g = (-1)^(N-|T|+1) ε_T` is correct: the coefficient of the target
simplex support function in `g` is one.

Each operator `I - ∂_(u_i)` preserves `V` and fixes the class of `h_P` modulo
`V`. Every earlier operator sends `h_(P_i)` to a linear combination of its
face support functions. A direction constant on `P_i` is constant on every
such descendant, so factor `i` kills that whole combination. Later factors
preserve zero. This proves annihilation without commuting the operators.
The strict dimension inequality supplies the required direction individually;
there is no missing simultaneous-genericity condition.

## Paper: reconstruction

For the two selected facets, the barycentric derivatives `b_j,b_l` have the
same nonzero sign. The hyperplane `b_l β_j - b_j β_l = 0` is parallel to the
sweep direction and cuts their opposite edge at
`β_j = b_j/(b_j+b_l)`, strictly between zero and one for either common sign.
Each piece loses exactly one nonparallel facet. Its other inherited facets
have the original outward-normal directions and signs.

The generic weighted simplex list retains all coefficients and repeated
occurrences. Grouping by normalized facet normals gives precisely the signed
facet contribution modulo a linear opposite-vertex term; nonfacet directions
are lower-dimensional. The common reconstruction operator therefore preserves
the cancellation. No logical gap or scope change was found.

## Lean: finite elimination and compatibility wrapper

`mem_GSpanRel_of_lt_finrank` uses the existing meanings of `FSpan`, `LSpan`,
`FaceClosed`, `GSpanRel`, and `germ`; none is weakened or redefined. It proves
membership in `GSpanRel` itself under the same strict dimension and
face-closure hypotheses as the old theorem. The absence of an extra linear
remainder is justified: the argument also annihilates zero-dimensional
summands, and a linear function is its own germ in every direction.

The finite-sup induction faithfully implements the paper's elimination.
`subsetSpan S` is deliberately larger than the span of actual faces of `S`;
this is harmless because all its generators are still fixed by a direction
annihilating `dir S`, and their germs remain in that same subset span. Germ
additivity is used only after establishing membership in `SSpan`, where the
existing theorem applies. Empty finite families reduce to the zero function.
The strict inequality `d < finrank U` already excludes `U = 0`, so the
choice of a direction not annihilating `U` introduces no hidden nonvacuity
assumption. All public parameters are explicitly typed.

`mem_GSpanRel_sup_of_lt_finrank` in `Faces.lean` keeps its old signature and
is now the immediate inclusion into `GSpanRel ⊔ LSpan 0`. Its consumers retain
their previous hypotheses and conclusions. The old peeling import remains
for compatibility, and the new leaf module does not import its aggregator.

## Reviewed snapshots

- `paper/main.tex`: SHA256 `a1162e0b72ed2503b37980b27ad28f755d54469bb059d547de06599ec9d8de68`.
- `MaxNN/Constructions/Paramid/Geom/Faces/Annihilate.lean`: SHA256 `a3e435c5707613d79ecb65e56e9eaedd95db0787984510d78fd1198a8795df5c`.
- `MaxNN/Constructions/Paramid/Geom/Faces.lean`: SHA256 `a0f335f4392e0ac519e6abdb670f1b29b705ee268e089ea2f9bb6c25599b49ae`.
