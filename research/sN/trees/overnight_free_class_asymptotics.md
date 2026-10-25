# Free canonical stars and matching-number-two trees cost no asymptotic rate

25 October 2026. Uniform mathematical consequence of the existing exact
separators, independently reviewed; not Lean verified.

The five-label canonical-star separator propagates by coordinate deletion
to every tied size m>=5. The seven-label separator in `overnight_lower.md`
propagates to every m>=7 for canonical tree face functions whose original
tree has matching number at most two. Leaf deletion cannot increase matching
number. Frozen components merely transport the canonical head; apex or
nonleaf deletions and proper faces have lower filtration degree.

At a tied locality, apply the corresponding separator. All functions in the
chosen free class vanish, while the target does not. Every remaining term
that survives must already pass the top-dimensional locality test used in
the counting proofs. Consequently a fixed-size count at m growing linearly
with N has exactly the same per-term capacities after either free class is
adjoined. Assign overlaps to the free class before counting; only terms
outside it are counted.

In particular, adjoin either free class to the original caterpillar and
specified rooted-star face dictionaries and to arbitrary-head, arbitrary-
weight comparison graphs of maximum degree at most Delta. For Delta<=3,
the number Z of terms outside the free class obeys

    Z=Omega((7/6)^N/sqrt(N)).

For fixed Delta>=4 it obeys

    Z=Omega_Delta((1+y_Delta)^N),
    y_Delta=(Delta-2)^(Delta-2)/(Delta-1)^(Delta-1).

Use m nearest N/7 in the first case and nearest N/(1+1/y_Delta) in the
second, exactly as in `overnight_upper_connected_coefficients.md`. These
sizes eventually exceed 5 or 7, so no new polynomial loss appears. Without
the added graph family the first bound applies to the original dictionary
alone, with either free class adjoined.

The same principle gives the stronger matching-mixture bounds in
`overnight_matching_mixture_mode.md`. Earlier N^4 or N^6 denominators came
from crude estimates of all small-arity exceptions in an all-arity sum;
they are not needed for these fixed-size asymptotic statements.

Scope: the free classes are canonical root-head, unit-length tree face
functions. Arbitrary real heads or comparison weights are allowed only in
the separately counted graph family, not in the free class. The result
does not include canonical trees of unbounded sublinear matching number.
