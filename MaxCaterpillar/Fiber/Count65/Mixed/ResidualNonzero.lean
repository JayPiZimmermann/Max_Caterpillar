import MaxCaterpillar.Fiber.Count65.Mixed.ResidualNonspan
import MaxCaterpillar.Fiber.Mixed65.FeatureSpace

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators

/-- Every exact three-core residual has a genuinely nonzero invariant
remainder, including every original orientation choice. -/
theorem ResidualSystem.exists_nonzero_base {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) :
    ∃ x : InvariantState, d.base t x.1 x.2.1 x.2.2 ≠ 0 := by
  classical
  by_contra hn
  obtain ⟨e,_,_,_,_,_,hnot⟩ := d.exists_full_span_normal_form t ht h hcard
  apply hnot
  refine ⟨fun _ => 0,?_⟩
  intro q b c
  have hz : d.base t q b c = 0 := by
    by_contra hz
    exact hn ⟨(q,b,c),hz⟩
  change d.base t q b c = _
  simp only [zero_mul,Finset.sum_const_zero]
  exact hz

end MaxCaterpillar.Fiber.Mixed65
