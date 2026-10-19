import MaxCaterpillar.Lemmas
import MaxCaterpillar.Asymptotics

/-! # The public theorem interface

The new construction is nonrecursive data; its correctness proof uses
induction. The width claims include all correction units.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

/-- For `N ≥ 3` this is `construction_width`; the arities `N ≤ 2` are covered
by the internal all-arity statement. -/
theorem maximum_width (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      ∀ x, net.eval x = Maximum N x := by
  rcases N with _ | _ | _ | r
  case succ.succ.succ => exact construction_width (r + 1) (Nat.le_add_left 1 r)
  all_goals exact Internal.secondWidth_eq _ ▸
    Internal.twoLayerWidth_iff.mp (Width.MAX_twoLayerWidth_caterpillar_spine_all _)

/-- The displayed width bounds grow quadratically and as `2^{O(N log N)}`,
respectively. The logarithmic formulation fixes the meaning of the latter. -/
theorem width_asymptotics :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => (firstWidth N : ℝ)) (fun N => (N : ℝ) ^ 2) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => Real.log (secondWidth N)) (fun N => (N : ℝ) * Real.log N) :=
  ⟨firstWidth_isBigO_square, log_secondWidth_isBigO_mul_log⟩

theorem network_correct (r : ℕ) (hr : 1 ≤ r) :
    ∀ x, (network r).eval x = Maximum (r + 1 + 1) x :=
  fun x => (network_eval_internal r x).trans (compactEssentialNetwork_computes r hr x)

end MaxCaterpillar
