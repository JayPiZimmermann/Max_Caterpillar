# Conditional all-tree exponential count from matching separators

25 October 2026. **Conditional result only.** The required uniform separators
have not been constructed. This note isolates the short counting argument
that would finish the unrestricted canonical all-tree exponential bound once
that analytic issue is resolved.

Assume that for every odd m>=5 there is a linear functional L_m on support
functions which:

1. annihilates the lower-dimensional span L_(m-2);
2. annihilates every canonical rooted oriented tree unit on m labels whose
   underlying tree on the m-1 nonapex labels has no perfect matching;
3. is nonzero on max_m.

Then every exact expansion of max_N by arbitrary canonical rooted oriented
tree units, their proper face functions, and a shallow remainder satisfies

    |K| >= [2^(N-1) - N - binom(N,3)] / [F_N - N + 1]    (N>=5),

where F_1=F_2=1. In particular |K|=Omega((2/phi)^N), where
phi=(1+sqrt(5))/2. Only full-dimensional units need to be counted in K.

## Which coordinate deletions can survive?

For each odd label subset S of size m>=5, apply the signed coordinate-deletion
operators to its complement in a fixed order, then apply L_m. These are
linear operators. They send max_N to max_m, so every such S needs at least
one original unit on which the composition is nonzero.

A full canonical unit has an apex a and a tree T on the other N-1 labels.
Deleting the apex gives a shallow germ. Deleting a vertex of current tree
degree at least two leaves at most n-4 free segments; its apex-base germ
therefore has dimension at most n-3, below the top dimension n-2 after
deleting one of the current n labels. Once a term drops into the lower
filtration, further coordinate deletions keep it there.

Thus every surviving step deletes a leaf. A non-head leaf gives the smaller
canonical unit up to sign and shallow terms. If the head is a leaf, the
only surviving orientation transfers the head to its neighbor; the other
orientation gives only lower-dimensional terms. These are the usual
coordinate-deletion rules, and they impose no restriction on the initial
root or edge orientations.

Consequently a nonzero final term requires a in S and a connected induced
subtree T[S minus {a}]. By the separator assumption, this even subtree must
have a perfect matching. Proper face functions already lie in L_(N-2), so
they contribute zero after the deletion composition and L_m.

The chosen deletion order may kill additional terms. No converse survival
claim is needed for the counting bound.

## Count the possible subsets for one unit

A forest has at most one perfect matching: the symmetric difference of two
distinct perfect matchings would contain a cycle. Associate to each detected
S the perfect matching of its retained subtree. Distinct S have different
matched vertex sets, so this is an injection into matchings of T with at
least two edges.

Every forest on n vertices has at most F_(n+1) matchings. For an isolated
vertex, remove it. Otherwise take a leaf v with neighbor u and partition
matchings according to whether they use uv:

    M(T)=M(T-v)+M(T-{u,v}) <= F_n+F_(n-1)=F_(n+1).

This induction applies to disconnected forests as well. A tree on N-1
vertices has one empty matching and N-2 single-edge matchings, hence at most
F_N-N+1 matchings with at least two edges.

Finally, the number of odd subsets S of size at least five is exactly
2^(N-1)-N-binom(N,3). Each needs a detecting unit, and each unit detects at
most F_N-N+1 of them. Double counting proves the displayed conditional bound.

## Outstanding hypothesis

The sparse signed-root score Q_* vanishes on nonmatchable trees and has a
nonzero necessary target response, but its proposed descent is now disproved:
the exact six-term identity in `overnight_uniform_q9.md` receives score -240.
The general uniform-separator hypothesis above remains open. The counting
argument must not be cited as an established unrestricted lower bound.
