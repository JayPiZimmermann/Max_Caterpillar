import MaxCaterpillar.CountCubic.ForestOrientation
import MaxCaterpillar.CountCubic.Chains
import MaxCaterpillar.CountCubic.StretchSum
import MaxCaterpillar.CountCubic.PathAlternation

/-! # Abstract order combinatorics for the cubic count

Root of the caterpillar-independent part of the cubic lower bound on `s_N`
(`research/sN/NOTE.md`, "Cubic claim C").

* `ForestOrientation`: on a finite rooted forest, two rank functions with the
  same number of forest neighbours above every vertex orient every edge alike
  (`orient_eq_of_upCount_eq`, `orient_eq_of_upCount_eq_all`).
* `Chains`: at most `m!/(a! b!)` total orders of an `m`-set list two disjoint
  chains of lengths `a`, `b` increasingly (`card_chainsOrdered_mul_le`,
  `card_chainsOrdered_div_le`).
* `StretchSum`: the stretch weight sums are at most `2` for every stretch
  length and leaf pattern (`stretchEdgeSum_le_two`, `stretchVertexSum_le_two`),
  with closed forms `sum_leafWeight`, `sum_spineWeight`.
* `PathAlternation`: tops (`pathUp = 0`), bottoms (`pathUp = 2`) and monotone
  vertices (`pathUp = 1`) on a path; tops and bottoms alternate
  (`exists_bottom_between_tops`, `exists_top_between_bottoms`), runs are
  monotone with at most one top (`monotone_of_run`, `top_unique_of_run`).
-/
