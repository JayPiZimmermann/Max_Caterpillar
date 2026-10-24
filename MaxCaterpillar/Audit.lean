import MaxCaterpillar.Audit.Expansion
import MaxCaterpillar.Audit.CaterpillarTree
import MaxCaterpillar.Audit.Widths
import MaxCaterpillar.Audit.TreeHyps

/-! # Semantic audit: nonvacuity and faithfulness of the public claims

* `Audit.exists_isCaterpillarExpansion`, `Audit.exists_isRootedStarExpansion`,
  `Audit.exists_isMixedExpansion`, `Audit.exists_isTreeExpansion`: the expansion hypotheses
  of the lower bounds are satisfiable for every `N`.
* `Audit.caterpillarFunction_eq_treeFace`: every caterpillar function is the face function
  `σ(x_root − x_apex + Σ edge terms)` of a tree face whose tree is a caterpillar.
* `Audit.second_width_half_succ_satisfiable_three/four`, `Audit.free_neurons_satisfiable`:
  witnesses for the hypotheses of the width theorems;
  `Audit.second_width_joint_hyp_false_three/four`: the hypothesis of `second_width_joint`
  fails for `N = 3, 4`.
-/
