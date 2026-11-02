import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.Normalization
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.CarrierPattern
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.Supports

/-! # The finite carrier roles are genuine physical network symmetries

Nonzero output magnitudes are absorbed by positive second-neuron scaling,
then an actual permutation of the five physical second neurons puts the shared,
exclusive, and invariant roles in positions 0, 1, 2, 3, 4. The first hidden layer,
function, biases-zero property, and all carrier zero incidences are preserved.
No analytic three-core extraction is assumed in this reindexing theorem.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open BigOperators MaxCaterpillar.Frontier

variable {N h₁ : ℕ}

/-- Positive output sign of an original physical neuron. -/
noncomputable def outputSign (net : Network N h₁ 5) (k : Fin 5) : Bool := by
  classical
  exact if 0 < net.w₃ k then true else false

lemma outputSign_true_iff (net : Network N h₁ 5) (k : Fin 5) :
    outputSign net k = true ↔ 0 < net.w₃ k := by
  classical
  simp [outputSign]

/-- Interpret a Boolean sign as an actual unit output coefficient. -/
def signValue : Bool → ℝ | false => -1 | true => 1

lemma signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> norm_num [signValue]

/-- These are exactly the existing positive scaling and hidden relabelling. -/
noncomputable def canonicalSecond (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5)) :
    Network N h₁ 5 :=
  permuteHidden (normalizeSecond net) (Equiv.refl (Fin h₁)) e

theorem canonicalSecond_eval (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (h : ∀ k, net.w₃ k ≠ 0) (x : Point N) :
    (canonicalSecond net e).eval x = net.eval x := by
  rw [canonicalSecond,permuteHidden_eval,normalizeSecond_eval net h]

theorem canonicalSecond_first (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5)) :
    (canonicalSecond net e).W₁ = net.W₁ ∧ (canonicalSecond net e).b₁ = net.b₁ := ⟨rfl,rfl⟩

lemma canonicalSecond_row (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (k : Fin 5) (j : Fin h₁) :
    (canonicalSecond net e).W₂ k j = |net.w₃ (e k)| * net.W₂ (e k) j := rfl

lemma canonicalSecond_bias (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5)) (k : Fin 5) :
    (canonicalSecond net e).b₂ k = |net.w₃ (e k)| * net.b₂ (e k) := rfl

lemma canonicalSecond_zero_iff (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin 5) (j : Fin h₁) :
    (canonicalSecond net e).W₂ k j = 0 ↔ net.W₂ (e k) j = 0 := by
  rw [canonicalSecond_row,mul_eq_zero]
  simp only [(abs_pos.mpr (h (e k))).ne',false_or]

/-- Output normalization and reindexing preserve every moving incidence. -/
theorem canonicalSecond_moving (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (h : ∀ k, net.w₃ k ≠ 0) (j : Fin h₁) :
    moving (fun k => (canonicalSecond net e).W₂ k j) =
      Finset.univ.filter (fun k => e k ∈ moving (fun i => net.W₂ i j)) := by
  classical
  ext k
  simp only [moving,Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr (canonicalSecond_zero_iff net e h k j)

theorem canonicalSecond_unit_output (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin 5) :
    (canonicalSecond net e).w₃ k = 1 ∨ (canonicalSecond net e).w₃ k = -1 :=
  normalizeSecond_unit_outputs net h (e k)

/-- The normalized coefficient carries precisely the original output sign. -/
theorem canonicalSecond_output_sign (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin 5) :
    (canonicalSecond net e).w₃ k = signValue (outputSign net (e k)) := by
  classical
  change net.w₃ (e k) / |net.w₃ (e k)| = signValue (outputSign net (e k))
  by_cases hp : 0 < net.w₃ (e k)
  · simp [outputSign,hp,signValue,abs_of_pos hp,div_self hp.ne']
  · rcases lt_or_gt_of_ne (h (e k)) with hn | hn
    · simp only [outputSign,if_neg hp,signValue]
      rw [abs_of_neg hn]
      field_simp [hn.ne]
    · exact False.elim (hp hn)

theorem canonicalSecond_zeroBiases (net : Network N h₁ 5) (e : Equiv.Perm (Fin 5))
    (h : net.HasZeroBiases) : (canonicalSecond net e).HasZeroBiases := by
  rcases h with ⟨h₁,h₂,h₃⟩
  refine ⟨?_,?_,?_⟩
  · simpa only [canonicalSecond,permuteHidden,normalizeSecond,scaleSecond] using h₁
  · funext k
    rw [canonicalSecond_bias,h₂]
    simp
  · exact h₃

/-- The normalized role conditions refer to the actual physical arrays. -/
structure CanonicalCarrierRoles (net : Network N h₁ 5) (p q : Fin h₁) : Prop where
  first_support : moving (fun k => net.W₂ k p) = {0,1}
  second_support : moving (fun k => net.W₂ k q) = {0,2}
  shared_unit : net.w₃ 0 = 1 ∨ net.w₃ 0 = -1
  first_exclusive : net.w₃ 1 = -net.w₃ 0
  second_exclusive : net.w₃ 2 = -net.w₃ 0
  first_invariant : net.w₃ 3 = 1
  second_invariant : net.w₃ 4 = net.w₃ 0

lemma CanonicalCarrierRoles.first_nonzero_iff {net : Network N h₁ 5} {p q : Fin h₁}
    (r : CanonicalCarrierRoles net p q) (k : Fin 5) :
    net.W₂ k p ≠ 0 ↔ k = 0 ∨ k = 1 := by
  classical
  have hh : k ∈ moving (fun i => net.W₂ i p) ↔ k = 0 ∨ k = 1 := by
    rw [r.first_support]
    simp
  simpa only [moving,Finset.mem_filter,Finset.mem_univ,true_and] using hh

lemma CanonicalCarrierRoles.second_nonzero_iff {net : Network N h₁ 5} {p q : Fin h₁}
    (r : CanonicalCarrierRoles net p q) (k : Fin 5) :
    net.W₂ k q ≠ 0 ↔ k = 0 ∨ k = 2 := by
  classical
  have hh : k ∈ moving (fun i => net.W₂ i q) ↔ k = 0 ∨ k = 2 := by
    rw [r.second_support]
    simp
  simpa only [moving,Finset.mem_filter,Finset.mem_univ,true_and] using hh

lemma CanonicalCarrierRoles.first_zero {net : Network N h₁ 5} {p q : Fin h₁}
    (r : CanonicalCarrierRoles net p q) (k : Fin 5) (h0 : k ≠ 0) (h1 : k ≠ 1) :
    net.W₂ k p = 0 := by
  by_contra hn
  exact (r.first_nonzero_iff k).mp hn |>.elim h0 h1

lemma CanonicalCarrierRoles.second_zero {net : Network N h₁ 5} {p q : Fin h₁}
    (r : CanonicalCarrierRoles net p q) (k : Fin 5) (h0 : k ≠ 0) (h2 : k ≠ 2) :
    net.W₂ k q = 0 := by
  by_contra hn
  exact (r.second_nonzero_iff k).mp hn |>.elim h0 h2

/-- A finite carrier pattern is realized by genuine positive scaling and a
permutation of the original physical neurons, preserving the first dictionary. -/
theorem exists_canonicalSecond_roles (net : Network N h₁ 5) (p q : Fin h₁)
    (h : ∀ k, net.w₃ k ≠ 0)
    (hp : (moving (fun k => net.W₂ k p)).card = 2)
    (hq : (moving (fun k => net.W₂ k q)).card = 2)
    (hu : (moving (fun k => net.W₂ k p) ∪ moving (fun k => net.W₂ k q)).card = 3)
    (hs : (Finset.univ.filter fun k => 0 < net.w₃ k).card = 3)
    (hsp : ((moving (fun k => net.W₂ k p)).filter fun k => 0 < net.w₃ k).card = 1)
    (hsq : ((moving (fun k => net.W₂ k q)).filter fun k => 0 < net.w₃ k).card = 1) :
    ∃ e : Equiv.Perm (Fin 5), CanonicalCarrierRoles (canonicalSecond net e) p q := by
  classical
  obtain ⟨e,heP,heQ,h1,h2,h3,h4⟩ := exists_signed_three_carrier_roles
    (moving (fun k => net.W₂ k p)) (moving (fun k => net.W₂ k q)) (outputSign net)
    hp hq hu (by simpa only [outputSign_true_iff] using hs)
    (by simpa only [outputSign_true_iff] using hsp)
    (by simpa only [outputSign_true_iff] using hsq)
  refine ⟨e,?_,?_,canonicalSecond_unit_output net e h 0,?_,?_,?_,?_⟩
  · rw [canonicalSecond_moving net e h p,heP]
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton,e.injective.eq_iff]
  · rw [canonicalSecond_moving net e h q,heQ]
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton,e.injective.eq_iff]
  · rw [canonicalSecond_output_sign net e h 1,canonicalSecond_output_sign net e h 0,h1,
      signValue_not]
  · rw [canonicalSecond_output_sign net e h 2,canonicalSecond_output_sign net e h 0,h2,
      signValue_not]
  · rw [canonicalSecond_output_sign net e h 3,h3]
    rfl
  · rw [canonicalSecond_output_sign net e h 4,canonicalSecond_output_sign net e h 0,h4]

/-- The same operation on the actual all-input exact fiber. -/
noncomputable def canonicalSecondFiber [NeZero N] (net : ExactFiber N h₁ 5)
    (h : ∀ k, net.val.w₃ k ≠ 0) (e : Equiv.Perm (Fin 5)) : ExactFiber N h₁ 5 :=
  permuteHiddenFiber (Equiv.refl (Fin h₁)) e
    (scaleSecondFiber (fun k => |net.val.w₃ k|) (fun k => abs_pos.mpr (h k)) net)

lemma canonicalSecondFiber_val [NeZero N] (net : ExactFiber N h₁ 5)
    (h : ∀ k, net.val.w₃ k ≠ 0) (e : Equiv.Perm (Fin 5)) :
    (canonicalSecondFiber net h e).val = canonicalSecond net.val e := rfl

/-- No equal-function shortcut is inserted into the symmetry quotient: this
is literally one positive scaling step and one hidden-permutation step. -/
theorem canonicalSecondFiber_same_quotient [NeZero N] (net : ExactFiber N h₁ 5)
    (h : ∀ k, net.val.w₃ k ≠ 0) (e : Equiv.Perm (Fin 5)) :
    quotientMk net = quotientMk (canonicalSecondFiber net h e) := by
  exact (quotientMk_eq_of_step (SymmetryStep.second net
    (fun k => |net.val.w₃ k|) (fun k => abs_pos.mpr (h k)))).trans
    (quotientMk_eq_of_step (SymmetryStep.hidden _ (Equiv.refl (Fin h₁)) e))

end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
