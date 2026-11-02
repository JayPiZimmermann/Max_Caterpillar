import MaxCaterpillar.Fiber.Count65.Mixed.SignDomains
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.HalfLineRigidity
import MaxCaterpillar.Fiber.Mixed65.FeatureSpace

/-! # From coefficient spans to actual invariant functions

The bridge uses the original four-feature function space and all real inputs.
No formal coefficient-space condition is substituted for functional equality.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Count65.PhysicalExtraction

lemma FormBothSignSpans.determinesPositive {t a b c d : ℝ}
    (hspan : FormBothSignSpans t a b c d) :
    DeterminesPositive (featureSpace t) (readout t a b c d) := by
  intro F hF hzero
  obtain ⟨A,B,C,D,hF⟩ := hF
  subst F
  have hz := (hspan A B C D).1 (by
    intro q v w hc
    exact hzero (q,v,w) hc)
  rcases hz with ⟨rfl,rfl,rfl,rfl⟩
  intro x
  simp [readout,form]

lemma FormBothSignSpans.determinesNegative {t a b c d : ℝ}
    (hspan : FormBothSignSpans t a b c d) :
    DeterminesNegative (featureSpace t) (readout t a b c d) := by
  intro F hF hzero
  obtain ⟨A,B,C,D,hF⟩ := hF
  subst F
  have hz := (hspan A B C D).2 (by
    intro q v w hc
    exact hzero (q,v,w) hc)
  rcases hz with ⟨rfl,rfl,rfl,rfl⟩
  intro x
  simp [readout,form]

lemma FormBothSignSpans.exists_positive {t a b c d : ℝ}
    (hspan : FormBothSignSpans t a b c d) :
    ∃ x : InvariantState, 0 < readout t a b c d x := by
  classical
  by_contra hn
  have hz := (hspan 0 0 1 0).1 (by
    intro q v w hc
    exact False.elim (hn ⟨(q,v,w),hc⟩))
  norm_num at hz

lemma FormBothSignSpans.exists_negative {t a b c d : ℝ}
    (hspan : FormBothSignSpans t a b c d) :
    ∃ x : InvariantState, readout t a b c d x < 0 := by
  classical
  by_contra hn
  have hz := (hspan 0 0 1 0).2 (by
    intro q v w hc
    exact False.elim (hn ⟨(q,v,w),hc⟩))
  norm_num at hz

end MaxCaterpillar.Fiber.Mixed65
