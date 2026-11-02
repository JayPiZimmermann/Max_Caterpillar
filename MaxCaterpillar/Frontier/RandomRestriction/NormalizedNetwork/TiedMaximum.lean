import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.DirectionRule

/-! # Exact MAX localization at a chosen tied coordinate set -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators Filter Topology
variable {N m h₁ h₂ : ℕ} [NeZero N] [NeZero m]

lemma tied_Maximum_zero (e : Fin m ↪ Fin N) (q : Point N)
    (hq : ∀ a, q (e a) = 0)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < 0) : Maximum N q = 0 := by
  classical
  apply Maximum_eq_of q 0 (e 0) (hq 0)
  intro i
  by_cases hi : i ∈ Finset.univ.image e
  · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    rw [hq a]
  · exact (hneg i hi).le

lemma eventually_tied_Maximum (e : Fin m ↪ Fin N) (q : Point N)
    (hq : ∀ a, q (e a) = 0)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < 0) (x : Point m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Maximum N (q + ε • lift e x) = ε * Maximum m x := by
  classical
  have hsmall : ∀ i : Fin N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      i ∉ Finset.univ.image e → |ε * Maximum m x| < -q i := by
    intro i
    by_cases hi : i ∈ Finset.univ.image e
    · exact Filter.eventually_of_forall (fun _ h => False.elim (h hi))
    · filter_upwards [eventually_small (Maximum m x) (neg_pos.mpr (hneg i hi))] with ε hε
      exact fun _ => hε
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [Filter.eventually_all.mpr hsmall,hpos] with ε hsmall hε
  obtain ⟨a,ha⟩ := exists_eq_Maximum x
  apply Maximum_eq_of _ _ (e a)
  · rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hq a,lift_selected,zero_add,←ha]
  · intro i
    by_cases hi : i ∈ Finset.univ.image e
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
      rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hq b,lift_selected,zero_add]
      exact mul_le_mul_of_nonneg_left (le_Maximum x b) hε.le
    · rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,lift_outside e x i hi,mul_zero,add_zero]
      have hh := (abs_lt.mp (hsmall i hi)).1
      linarith only [hh]

/-- An actual all-input MAX identity localizes to the exact smaller MAX
function. No normal-form or genericity assumption is needed for this step. -/
theorem directional_computes_max_of_tied (net : NormalizedNetwork N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (e : Fin m ↪ Fin N) (q : Point N)
    (hq : ∀ a, q (e a) = 0)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < 0) :
    ∀ x, net.directionalEval q e x = Maximum m x := by
  intro x
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,htarget,hdir⟩ :=
    (hpos.and ((eventually_tied_Maximum e q hq hneg x).and
      (net.eventually_eval_direction q e x))).exists
  have hbase : net.eval q = 0 := (hnet q).trans (tied_Maximum_zero e q hq hneg)
  rw [hbase,zero_add,hnet] at hdir
  exact mul_left_cancel₀ hε.ne' (hdir.symm.trans htarget)

#check @directional_computes_max_of_tied
#print axioms directional_computes_max_of_tied
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
