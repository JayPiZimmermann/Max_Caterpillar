import Mathlib

/- Elementary arithmetic control only. The max4 germ and Boolean
   coefficient bridge are stated in the accompanying written proof. -/
namespace OvernightCompleteFourSign

theorem negative_single_fold_impossible (P Q : ℝ) (hP : 0 ≤ P)
    (h3 : 2*Q-3*P=4) (h4 : Q-P=1) : False := by
  linarith

#print axioms negative_single_fold_impossible
end OvernightCompleteFourSign
