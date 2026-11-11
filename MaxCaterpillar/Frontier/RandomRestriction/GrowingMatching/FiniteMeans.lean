import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.TailEnvelope

/-! Literal finite product means and event fractions. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators

theorem meanOver_prod {A B : Type*} [Fintype A] [Fintype B] (f : A×B→ℝ) :
    meanOver f=meanOver (fun a=>meanOver (fun b=>f (a,b))) := by
  unfold meanOver
  simp only [Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem meanOver_comm {A B : Type*} [Fintype A] [Fintype B] (f : A→B→ℝ) :
    meanOver (fun a=>meanOver (f a))=meanOver (fun b=>meanOver (fun a=>f a b)) := by
  unfold meanOver
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem meanOver_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (E : Finset Ω) :
    meanOver (fun ω=>if ω∈E then (1:ℝ) else 0)=
      (E.card:ℝ)/(Fintype.card Ω:ℝ) := by
  classical
  unfold meanOver
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,mul_one]
  ring

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
