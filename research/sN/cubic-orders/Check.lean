import MaxCaterpillar.CountCubic.Orders
open MaxCaterpillar.CountCubic
#check @orient_eq_of_upCount_eq
#check @orient_eq_of_upCount_eq_all
#check @card_chainsOrdered_mul_le
#check @card_chainsOrdered_div_le
#check @stretchEdgeSum_le_two
#check @stretchVertexSum_le_two
#check @sum_leafWeight
#check @sum_spineWeight
#check @core_le_two
#check @pathUp_eq_zero_iff
#check @pathUp_eq_two_iff
#check @pathUp_eq_one_iff
#check @exists_bottom_between_tops
#check @exists_top_between_bottoms
#check @monotone_of_run
#check @top_unique_of_run
#print axioms orient_eq_of_upCount_eq_all
#print axioms orient_eq_of_upCount_eq
#print axioms card_chainsOrdered_div_le
#print axioms stretchEdgeSum_le_two
#print axioms stretchVertexSum_le_two
#print axioms sum_spineWeight
#print axioms top_unique_of_run
#print axioms monotone_of_run
#print axioms exists_top_between_bottoms
#print axioms pathUp_eq_one_iff
-- nonvacuity sanity: concrete evaluations
example : stretchEdgeSum 3 (fun _ => 0) = 2 := by
  unfold stretchEdgeSum spineWeight
  rw [Finset.sum_Ico_succ_top (by norm_num), Finset.sum_Ico_succ_top (by norm_num),
    Finset.Ico_self, Finset.sum_empty]
  norm_num [Nat.factorial]
example : stretchEdgeSum 2 (fun _ => 1) = 2 := by
  unfold stretchEdgeSum leafWeight
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_succ_top (by norm_num),
    Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty]
  norm_num [Nat.factorial]
