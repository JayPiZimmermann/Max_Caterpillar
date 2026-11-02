import MaxCaterpillar.Frontier.Asymptotics
import Mathlib

/-! # A nonzero invariant first row vanishes at every three-way top tie

At q=-e_i, Max4 has three tied maximizers. If every invariant row vanishing
there were zero, the entire asymptotic network would have a linear local odd
part. This contradicts the existing three-way-tie obstruction.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open BigOperators Frontier

/-- Every input coordinate is omitted by a nonzero invariant first-layer row.
This holds at any finite second hidden width, without a first-width restriction. -/
theorem invariant_row_omits_coordinate {h₁ h₂ : ℕ}
    (net : ZNet 4 h₁ h₂) (hnet : ∀ x, net.eval x = Maximum 4 x) (i : Fin 4) :
    ∃ j, net.s j = 0 ∧ net.A j i = 0 ∧ net.A j ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ j, net.s j = 0 → net.A j i = 0 → net.A j = 0 := by
    intro j hs hi
    by_contra hA
    exact hn ⟨j, hs, hi, hA⟩
  let q : Point 4 := -unitVec i
  have hrow : ∀ j, LocAff (fun x =>
      pick (net.s j) (lin (net.A j) x) (relu (lin (net.A j) x))) q := by
    intro j
    rcases lt_trichotomy (net.s j) 0 with hs | hs | hs
    · exact (locAff_const 0 q).congr fun x => by simp [pick, hs, not_lt.mpr hs.le]
    · by_cases hA : net.A j = 0
      · exact (locAff_const 0 q).congr fun x => by simp [pick, hs, hA, lin_zero_left, relu]
      · have hi : net.A j i ≠ 0 := fun hi => hA (hzero j hs hi)
        have hq : lin (net.A j) q ≠ 0 := by
          simpa only [q, lin_neg_right, lin_unitVec, neg_ne_zero] using hi
        exact ((locAff_lin (net.A j) q).reluComp hq).congr fun x => by simp [pick, hs]
    · exact (locAff_lin (net.A j) q).congr fun x => by simp [pick, hs]
  have hG : ∀ k, LocAff (net.Gp k) q := fun k =>
    LocAff.sum _ fun j _ => (hrow j).const_mul (net.W k j)
  have hrest : LocOddLin net.rest q := by
    apply LocOddLin.sum
    intro k _
    rcases lt_trichotomy (net.Tp k) 0 with hT | hT | hT
    · exact (locOddLin_const 0 q).congr fun x => by simp [pick, hT, not_lt.mpr hT.le]
    · exact ((hG k).relu_locOddLin.const_mul (net.d k)).congr fun x => by simp [pick, hT]
    · exact ((hG k).locOddLin.const_mul (net.d k)).congr fun x => by simp [pick, hT]
  have hmax := hrest.congr fun x => (net.max_plus hnet).2 x |>.symm
  apply not_locOddLin_max q (Finset.univ.erase i) (by simp) ?_ ?_ hmax
  · intro k hk
    simp [q, unitVec, Finset.ne_of_mem_erase hk]
  · intro k hk
    have hi : k = i := by simpa using hk
    subst k
    simp [q, unitVec]

/-- The same necessary condition on the actual first matrix allows arbitrary biases. -/
theorem network_invariant_row_omits_coordinate {h₁ h₂ : ℕ}
    (net : Network 4 h₁ h₂) (hnet : ∀ x, net.eval x = Maximum 4 x) (i : Fin 4) :
    ∃ j, (∑ k, net.W₁ j k) = 0 ∧ net.W₁ j i = 0 ∧ net.W₁ j ≠ 0 := by
  simpa only [Network.toZ, ZNet.s] using
    invariant_row_omits_coordinate net.toZ (net.toZ_eval_of_max hnet) i

#print axioms invariant_row_omits_coordinate
#print axioms network_invariant_row_omits_coordinate
end MaxCaterpillar.Fiber.Count65
