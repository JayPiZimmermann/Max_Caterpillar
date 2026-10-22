import MaxNN.Core.Max
import MaxNN.Constructions.MaxN.Width.Layer.Features
import Mathlib.Tactic

/-! # A six-point test functional for the face-function count

A unit description in full coordinates is an integer head `h` and a finite set
`M` of ordered pairs; its face function is
`U(y) = σ(∑ₒ hₒ yₒ + ∑_{(i,j) ∈ M} σ(y_i - y_j))`.

For a three-set `T`, a base `B` and two distinct points `a, b ∈ T`, the base
point puts `0` on `T` and `-B^(o+1)` on every other coordinate `o`; the stencil
moves only the coordinates `a` and `b`.  The six-point functional `Λ` kills
every function of the first hidden layer, takes the value `2η` on the maximum,
and vanishes on a face function unless its preactivation is zero at the base
point and it has a pair inside `T` or a generic local head.
-/

open BigOperators

namespace MaxCaterpillar.CountLower

open MaxNN MaxNN.Width

variable {N : ℕ}

/-- A face-function description in full coordinates: an integer head and the
ordered pairs `(i, j)` of its functions `σ(y_i - y_j)`. -/
structure Descr (N : ℕ) where
  h : Fin N → ℤ
  M : Finset (Fin N × Fin N)

namespace Descr

/-- The preactivation `∑ₒ hₒ yₒ + ∑_{(i,j) ∈ M} σ(y_i - y_j)`. -/
noncomputable def arg (D : Descr N) (y : Fin N → ℝ) : ℝ :=
  ∑ o, (D.h o : ℝ) * y o + ∑ m in D.M, relu (y m.1 - y m.2)

/-- The face function `σ(arg)`. -/
noncomputable def unit (D : Descr N) (y : Fin N → ℝ) : ℝ := relu (D.arg y)

/-- The preactivation at an integer point. -/
def argZ (D : Descr N) (z : Fin N → ℤ) : ℤ :=
  ∑ o, D.h o * z o + ∑ m in D.M, max 0 (z m.1 - z m.2)

theorem arg_intCast (D : Descr N) (z : Fin N → ℤ) :
    D.arg (fun o => (z o : ℝ)) = (D.argZ z : ℝ) := by
  unfold arg argZ relu
  push_cast
  rfl

end Descr

/-! ## The six-point functional on functions of two variables -/

/-- `J(q₊) - J(q₋)` with `q± = ±2η (1, 1)` and step `η (1, -1)`. -/
noncomputable def Φ (η : ℝ) (φ : ℝ → ℝ → ℝ) : ℝ :=
  φ (3 * η) η + φ η (3 * η) - 2 * φ (2 * η) (2 * η)
    - φ (-η) (-(3 * η)) - φ (-(3 * η)) (-η) + 2 * φ (-(2 * η)) (-(2 * η))

theorem Φ_congr {η : ℝ} (hη : 0 ≤ η) {φ ψ : ℝ → ℝ → ℝ}
    (h : ∀ α β, |α| ≤ 3 * η → |β| ≤ 3 * η → φ α β = ψ α β) : Φ η φ = Φ η ψ := by
  have hb : ∀ x : ℝ, -(3 * η) ≤ x → x ≤ 3 * η → |x| ≤ 3 * η :=
    fun x h1 h2 => abs_le.mpr ⟨h1, h2⟩
  unfold Φ
  rw [h (3 * η) η (hb _ (by linarith) (by linarith)) (hb _ (by linarith) (by linarith)),
    h η (3 * η) (hb _ (by linarith) (by linarith)) (hb _ (by linarith) (by linarith)),
    h (2 * η) (2 * η) (hb _ (by linarith) (by linarith)) (hb _ (by linarith) (by linarith)),
    h (-η) (-(3 * η)) (hb _ (by linarith) (by linarith)) (hb _ (by linarith) (by linarith)),
    h (-(3 * η)) (-η) (hb _ (by linarith) (by linarith)) (hb _ (by linarith) (by linarith)),
    h (-(2 * η)) (-(2 * η)) (hb _ (by linarith) (by linarith))
      (hb _ (by linarith) (by linarith))]

theorem Φ_affine (η c₀ c₁ c₂ : ℝ) : Φ η (fun α β => c₀ + c₁ * α + c₂ * β) = 0 := by
  unfold Φ
  ring

theorem Φ_const (η c : ℝ) : Φ η (fun _ _ => c) = 0 := by
  unfold Φ
  ring

theorem Φ_add (η : ℝ) (φ ψ : ℝ → ℝ → ℝ) :
    Φ η (fun α β => φ α β + ψ α β) = Φ η φ + Φ η ψ := by
  unfold Φ
  ring

theorem Φ_mul (η c : ℝ) (φ : ℝ → ℝ → ℝ) :
    Φ η (fun α β => c * φ α β) = c * Φ η φ := by
  unfold Φ
  ring

theorem Φ_sum {ι : Type*} (η : ℝ) (s : Finset ι) (f : ι → ℝ → ℝ → ℝ) :
    Φ η (fun α β => ∑ i in s, f i α β) = ∑ i in s, Φ η (f i) := by
  unfold Φ
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem Φ_ite (η : ℝ) (p : Prop) [Decidable p] (φ : ℝ → ℝ → ℝ) (h : p → Φ η φ = 0) :
    Φ η (fun α β => if p then φ α β else 0) = 0 := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact h hp
  · simp only [if_neg hp]
    exact Φ_const η 0

/-- The one-variable combination behind `Φ (σ(c α)) = 0`. -/
theorem relu_comb (η c : ℝ) (hη : 0 ≤ η) :
    relu (c * (3 * η)) + relu (c * η) - 2 * relu (c * (2 * η)) - relu (c * -η)
      - relu (c * -(3 * η)) + 2 * relu (c * -(2 * η)) = 0 := by
  rcases le_total 0 c with hc | hc
  · rw [relu_of_nonneg (show 0 ≤ c * (3 * η) by positivity),
      relu_of_nonneg (show 0 ≤ c * η by positivity),
      relu_of_nonneg (show 0 ≤ c * (2 * η) by positivity),
      relu_of_nonpos (show c * -η ≤ 0 by nlinarith),
      relu_of_nonpos (show c * -(3 * η) ≤ 0 by nlinarith),
      relu_of_nonpos (show c * -(2 * η) ≤ 0 by nlinarith)]
    ring
  · rw [relu_of_nonpos (show c * (3 * η) ≤ 0 by nlinarith),
      relu_of_nonpos (show c * η ≤ 0 by nlinarith),
      relu_of_nonpos (show c * (2 * η) ≤ 0 by nlinarith),
      relu_of_nonneg (show 0 ≤ c * -η by nlinarith),
      relu_of_nonneg (show 0 ≤ c * -(3 * η) by nlinarith),
      relu_of_nonneg (show 0 ≤ c * -(2 * η) by nlinarith)]
    ring

/-- `Φ` kills `σ(c₁ α + c₂ β)` when the normal is a multiple of a root
`e_a`, `e_b` or `e_a - e_b`. -/
theorem Φ_relu_lin {η : ℝ} (hη : 0 ≤ η) (c₁ c₂ : ℝ)
    (h : c₁ = 0 ∨ c₂ = 0 ∨ c₁ + c₂ = 0) :
    Φ η (fun α β => relu (c₁ * α + c₂ * β)) = 0 := by
  rcases h with h | h | h
  · subst h
    unfold Φ
    simp only [zero_mul, zero_add]
    linarith [relu_comb η c₂ hη]
  · subst h
    unfold Φ
    simp only [zero_mul, add_zero]
    linarith [relu_comb η c₁ hη]
  · have h2 : c₂ = -c₁ := by linarith
    subst h2
    unfold Φ
    ring_nf


/-! ## The stencil around a three-set -/

/-- The base point: `0` on `T` and `-B^(o+1)` at every other coordinate `o`. -/
def baseZ (T : Finset (Fin N)) (B : ℕ) (o : Fin N) : ℤ :=
  if o ∈ T then 0 else -((B : ℤ) ^ (o.val + 1))

/-- The stencil point: the base point with `α` added at `a` and `β` at `b`. -/
noncomputable def pt (T : Finset (Fin N)) (B : ℕ) (a b : Fin N) (α β : ℝ) (o : Fin N) : ℝ :=
  (baseZ T B o : ℝ) + (if o = a then α else 0) + (if o = b then β else 0)

/-- The test functional of a three-set with moving coordinates `a`, `b`. -/
noncomputable def Λ (T : Finset (Fin N)) (B : ℕ) (a b : Fin N) (η : ℝ)
    (g : (Fin N → ℝ) → ℝ) : ℝ :=
  Φ η (fun α β => g (pt T B a b α β))

/-- The indicator of a coordinate. -/
noncomputable def χ (a o : Fin N) : ℝ := if o = a then 1 else 0

section Stencil

variable {T : Finset (Fin N)} {B : ℕ} {a b : Fin N}

theorem baseZ_of_mem {o : Fin N} (ho : o ∈ T) : baseZ T B o = 0 := if_pos ho

theorem baseZ_le {o : Fin N} (hB : 1 ≤ B) (ho : o ∉ T) : (baseZ T B o : ℝ) ≤ -B := by
  unfold baseZ
  rw [if_neg ho]
  push_cast
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have := le_self_pow hB' (show o.val + 1 ≠ 0 by omega)
  linarith

theorem baseZ_nonpos (o : Fin N) : (baseZ T B o : ℝ) ≤ 0 := by
  unfold baseZ
  split_ifs
  · norm_num
  · push_cast
    have : (0 : ℝ) ≤ (B : ℝ) ^ (o.val + 1) := by positivity
    linarith

theorem pt_of_mem {o : Fin N} (ho : o ∈ T) (α β : ℝ) :
    pt T B a b α β o = χ a o * α + χ b o * β := by
  unfold pt χ
  rw [baseZ_of_mem ho]
  split_ifs <;> push_cast <;> ring

theorem pt_of_not_mem (ha : a ∈ T) (hb : b ∈ T) {o : Fin N} (ho : o ∉ T) (α β : ℝ) :
    pt T B a b α β o = baseZ T B o := by
  have hoa : o ≠ a := fun h => ho (h ▸ ha)
  have hob : o ≠ b := fun h => ho (h ▸ hb)
  unfold pt
  rw [if_neg hoa, if_neg hob]
  ring

theorem pt_zero (o : Fin N) : pt T B a b 0 0 o = baseZ T B o := by
  unfold pt
  split_ifs <;> ring

theorem pt_a (ha : a ∈ T) (hab : a ≠ b) (α β : ℝ) : pt T B a b α β a = α := by
  rw [pt_of_mem ha]
  unfold χ
  rw [if_pos rfl, if_neg hab]
  ring

theorem pt_b (hb : b ∈ T) (hab : a ≠ b) (α β : ℝ) : pt T B a b α β b = β := by
  rw [pt_of_mem hb]
  unfold χ
  rw [if_pos rfl, if_neg (Ne.symm hab)]
  ring

theorem pt_c {c : Fin N} (hc : c ∈ T) (hca : c ≠ a) (hcb : c ≠ b) (α β : ℝ) :
    pt T B a b α β c = 0 := by
  rw [pt_of_mem hc]
  unfold χ
  rw [if_neg hca, if_neg hcb]
  ring

theorem chi_single (hab : a ≠ b) (o : Fin N) : χ a o = 0 ∨ χ b o = 0 := by
  unfold χ
  by_cases hoa : o = a
  · right
    rw [if_neg (fun h => hab (hoa.symm.trans h))]
  · left
    rw [if_neg hoa]

theorem chi_pair (hab : a ≠ b) (i j : Fin N) :
    χ a i - χ a j = 0 ∨ χ b i - χ b j = 0 ∨ χ a i - χ a j + (χ b i - χ b j) = 0 := by
  unfold χ
  by_cases hia : i = a <;> by_cases hib : i = b <;> by_cases hja : j = a <;>
    by_cases hjb : j = b <;> simp [hia, hib, hja, hjb, hab, Ne.symm hab]

theorem abs_pt_le (hab : a ≠ b) {o : Fin N} (ho : o ∈ T) {α β s : ℝ} (hs : 0 ≤ s)
    (hα : |α| ≤ s) (hβ : |β| ≤ s) : |pt T B a b α β o| ≤ s := by
  rw [pt_of_mem ho]
  unfold χ
  by_cases hoa : o = a
  · rw [if_pos hoa, if_neg (fun h => hab (hoa.symm.trans h))]
    simpa using hα
  · rw [if_neg hoa]
    split_ifs
    · simpa using hβ
    · simpa using hs

/-- A function `σ(y_i - y_j)` is killed by the stencil functional. -/
theorem Φ_relu_pt_pair {η : ℝ} (hη : 0 ≤ η) (hη1 : 3 * η ≤ 1) (hB : 2 ≤ B)
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (i j : Fin N) :
    Φ η (fun α β => relu (pt T B a b α β i - pt T B a b α β j)) = 0 := by
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
  · have e : (fun α β => relu (pt T B a b α β i - pt T B a b α β j)) =
        fun α β => relu ((χ a i - χ a j) * α + (χ b i - χ b j) * β) := by
      funext α β
      rw [pt_of_mem hi, pt_of_mem hj]
      ring_nf
    rw [e]
    exact Φ_relu_lin hη _ _ (chi_pair hab i j)
  · rw [Φ_congr hη (ψ := fun α β => -(baseZ T B j : ℝ) + χ a i * α + χ b i * β)]
    · exact Φ_affine η _ _ _
    intro α β hα hβ
    have h1 := abs_pt_le (B := B) hab hi (by linarith) hα hβ
    have h2 := baseZ_le (B := B) hB1 hj
    rw [pt_of_not_mem ha hb hj, relu_of_nonneg (by linarith [(abs_le.mp h1).1]),
      pt_of_mem hi]
    ring
  · rw [Φ_congr hη (ψ := fun _ _ => 0)]
    · exact Φ_const η 0
    intro α β hα hβ
    have h1 := abs_pt_le (B := B) hab hj (by linarith) hα hβ
    have h2 := baseZ_le (B := B) hB1 hi
    rw [pt_of_not_mem ha hb hi, relu_of_nonpos (by linarith [(abs_le.mp h1).1])]
  · have e : (fun α β => relu (pt T B a b α β i - pt T B a b α β j)) =
        fun _ _ => relu ((baseZ T B i : ℝ) - baseZ T B j) := by
      funext α β
      rw [pt_of_not_mem ha hb hi, pt_of_not_mem ha hb hj]
    rw [e]
    exact Φ_const η _

/-- A function `σ(s y_i)` is killed by the stencil functional. -/
theorem Φ_relu_pt {η : ℝ} (hη : 0 ≤ η) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
    (s : ℝ) (i : Fin N) :
    Φ η (fun α β => relu (s * pt T B a b α β i)) = 0 := by
  by_cases hi : i ∈ T
  · have e : (fun α β => relu (s * pt T B a b α β i)) =
        fun α β => relu ((s * χ a i) * α + (s * χ b i) * β) := by
      funext α β
      rw [pt_of_mem hi]
      ring_nf
    rw [e]
    apply Φ_relu_lin hη
    rcases chi_single hab i with h | h
    · left; rw [h, mul_zero]
    · right; left; rw [h, mul_zero]
  · have e : (fun α β => relu (s * pt T B a b α β i)) =
        fun _ _ => relu (s * (baseZ T B i : ℝ)) := by
      funext α β
      rw [pt_of_not_mem ha hb hi]
    rw [e]
    exact Φ_const η _

/-- **Step 1.** The functional kills every neuron of the first hidden layer. -/
theorem Λ_feat {η : ℝ} (hη : 0 ≤ η) (hη1 : 3 * η ≤ 1) (hB : 2 ≤ B)
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (j : Fin (W N)) :
    Λ T B a b η (fun x => feat N x j) = 0 := by
  unfold Λ
  refine Fin.addCases (motive := fun j : Fin (N + (N + N.choose 2)) =>
      Φ η (fun α β => feat N (pt T B a b α β) j) = 0) (fun i => ?_) (fun j => ?_) j
  · have h : (fun α β => feat N (pt T B a b α β) (Fin.castAdd _ i)) =
        fun α β => relu (1 * pt T B a b α β i) := by
      funext α β
      rw [one_mul]
      exact feat_pos _ i
    show Φ η (fun α β => feat N (pt T B a b α β) (Fin.castAdd _ i)) = 0
    rw [h]
    exact Φ_relu_pt hη ha hb hab 1 i
  · refine Fin.addCases (motive := fun j : Fin (N + N.choose 2) =>
      Φ η (fun α β => feat N (pt T B a b α β) (Fin.natAdd _ j)) = 0)
      (fun i => ?_) (fun q => ?_) j
    · have h : (fun α β => feat N (pt T B a b α β) (Fin.natAdd _ (Fin.castAdd _ i))) =
          fun α β => relu (-1 * pt T B a b α β i) := by
        funext α β
        rw [neg_one_mul]
        exact feat_neg _ i
      show Φ η (fun α β => feat N (pt T B a b α β) (Fin.natAdd _ (Fin.castAdd _ i))) = 0
      rw [h]
      exact Φ_relu_pt hη ha hb hab (-1) i
    · have h : (fun α β => feat N (pt T B a b α β) (Fin.natAdd _ (Fin.natAdd _ q))) =
          fun α β => relu (pt T B a b α β (prFst q) - pt T B a b α β (prSnd q)) := by
        funext α β
        exact feat_pr _ q
      show Φ η (fun α β => feat N (pt T B a b α β) (Fin.natAdd _ (Fin.natAdd _ q))) = 0
      rw [h]
      exact Φ_relu_pt_pair hη hη1 hB ha hb hab _ _

/-- The auxiliary span is killed. -/
theorem Λ_auxiliary {η : ℝ} (hη : 0 ≤ η) (hη1 : 3 * η ≤ 1) (hB : 2 ≤ B)
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (w : Fin (W N) → ℝ) :
    Λ T B a b η (fun x => ∑ j, w j * feat N x j) = 0 := by
  unfold Λ
  rw [Φ_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Φ_mul]
  have h := Λ_feat hη hη1 hB ha hb hab j
  unfold Λ at h
  rw [h, mul_zero]

theorem pt_le {α β v : ℝ} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (hv : 0 ≤ v)
    (hα : α ≤ v) (hβ : β ≤ v) (o : Fin N) : pt T B a b α β o ≤ v := by
  by_cases hoa : o = a
  · subst hoa
    rw [pt_a ha hab]
    exact hα
  by_cases hob : o = b
  · subst hob
    rw [pt_b hb hab]
    exact hβ
  unfold pt
  rw [if_neg hoa, if_neg hob]
  linarith [baseZ_nonpos (T := T) (B := B) o]

/-- **Step 2.** The functional takes the value `2η` on the maximum. -/
theorem Λ_MAX [NeZero N] {η : ℝ} (hη : 0 ≤ η) {c : Fin N}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Λ T B a b η (MAX N) = 2 * η := by
  have hval : ∀ α β v : ℝ, 0 ≤ v → α ≤ v → β ≤ v → (α = v ∨ β = v ∨ v = 0) →
      MAX N (pt T B a b α β) = v := by
    intro α β v hv hα hβ he
    refine le_antisymm (MAX_le (pt_le ha hb hab hv hα hβ)) ?_
    rcases he with he | he | he
    · calc v = pt T B a b α β a := by rw [pt_a ha hab, he]
        _ ≤ _ := le_MAX N _ a
    · calc v = pt T B a b α β b := by rw [pt_b hb hab, he]
        _ ≤ _ := le_MAX N _ b
    · calc v = pt T B a b α β c := by rw [pt_c hc hca hcb, he]
        _ ≤ _ := le_MAX N _ c
  unfold Λ Φ
  beta_reduce
  rw [hval (3 * η) η (3 * η) (by linarith) le_rfl (by linarith) (Or.inl rfl),
    hval η (3 * η) (3 * η) (by linarith) (by linarith) le_rfl (Or.inr (Or.inl rfl)),
    hval (2 * η) (2 * η) (2 * η) (by linarith) le_rfl le_rfl (Or.inl rfl),
    hval (-η) (-(3 * η)) 0 le_rfl (by linarith) (by linarith) (Or.inr (Or.inr rfl)),
    hval (-(3 * η)) (-η) 0 le_rfl (by linarith) (by linarith) (Or.inr (Or.inr rfl)),
    hval (-(2 * η)) (-(2 * η)) 0 le_rfl (by linarith) (by linarith) (Or.inr (Or.inr rfl))]
  ring

end Stencil

/-! ## Face functions on the stencil (step 3) -/

/-- The number of pairs `(t, o) ∈ M` with `o ∉ T`. -/
def outZ (D : Descr N) (T : Finset (Fin N)) (t : Fin N) : ℤ :=
  ∑ m in D.M, if m.1 = t ∧ m.2 ∉ T then 1 else 0

/-- The local head `v_t = h_t + #{o ∉ T : (t, o) ∈ M}`. -/
def vZ (D : Descr N) (T : Finset (Fin N)) (t : Fin N) : ℤ := D.h t + outZ D T t

/-- Some pair of `M` lies inside `T`. -/
def PairIn (D : Descr N) (T : Finset (Fin N)) : Prop := ∃ m ∈ D.M, m.1 ∈ T ∧ m.2 ∈ T

theorem outZ_nonneg (D : Descr N) (T : Finset (Fin N)) (t : Fin N) : 0 ≤ outZ D T t :=
  Finset.sum_nonneg fun m _ => by split_ifs <;> norm_num

theorem outZ_le (D : Descr N) (T : Finset (Fin N)) (t : Fin N) :
    outZ D T t ≤ D.M.card := by
  unfold outZ
  calc (∑ m in D.M, if m.1 = t ∧ m.2 ∉ T then (1 : ℤ) else 0) ≤ ∑ _m in D.M, (1 : ℤ) :=
        Finset.sum_le_sum fun m _ => by split_ifs <;> norm_num
    _ = D.M.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

section Units

variable {T : Finset (Fin N)} {B : ℕ} {a b : Fin N}

theorem relu_pt_split (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (hB : 2 ≤ B) {α β : ℝ}
    (hα : |α| ≤ 1) (hβ : |β| ≤ 1) (i j : Fin N) :
    relu (pt T B a b α β i - pt T B a b α β j) =
      relu ((baseZ T B i : ℝ) - baseZ T B j) +
        (if i ∈ T ∧ j ∉ T then χ a i * α + χ b i * β else 0) +
        (if i ∈ T ∧ j ∈ T then relu (pt T B a b α β i - pt T B a b α β j) else 0) := by
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
  · rw [if_neg (fun h => h.2 hj), if_pos ⟨hi, hj⟩, baseZ_of_mem hi, baseZ_of_mem hj,
      Int.cast_zero, sub_self, relu_of_nonpos (le_refl (0 : ℝ))]
    ring
  · have h1 := abs_pt_le (B := B) hab hi zero_le_one hα hβ
    have h2 := baseZ_le (B := B) hB1 hj
    rw [if_pos ⟨hi, hj⟩, if_neg (fun h => hj h.2), pt_of_not_mem ha hb hj, baseZ_of_mem hi,
      relu_of_nonneg (show (0 : ℝ) ≤ pt T B a b α β i - baseZ T B j by
        linarith [(abs_le.mp h1).1]),
      Int.cast_zero, relu_of_nonneg (show (0 : ℝ) ≤ 0 - baseZ T B j by linarith),
      pt_of_mem hi]
    ring
  · have h1 := abs_pt_le (B := B) hab hj zero_le_one hα hβ
    have h2 := baseZ_le (B := B) hB1 hi
    rw [if_neg (fun h => hi h.1), if_neg (fun h => hi h.1), pt_of_not_mem ha hb hi,
      baseZ_of_mem hj,
      relu_of_nonpos (show (baseZ T B i : ℝ) - pt T B a b α β j ≤ 0 by
        linarith [(abs_le.mp h1).1]),
      Int.cast_zero, relu_of_nonpos (show (baseZ T B i : ℝ) - 0 ≤ 0 by linarith)]
    ring
  · rw [if_neg (fun h => hi h.1), if_neg (fun h => hi h.1), pt_of_not_mem ha hb hi,
      pt_of_not_mem ha hb hj]
    ring

theorem sum_h_pt (D : Descr N) (α β : ℝ) :
    ∑ o, (D.h o : ℝ) * pt T B a b α β o =
      ∑ o, (D.h o : ℝ) * (baseZ T B o : ℝ) + D.h a * α + D.h b * β := by
  unfold pt
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem sum_out (D : Descr N) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (α β : ℝ) :
    ∑ m in D.M, (if m.1 ∈ T ∧ m.2 ∉ T then χ a m.1 * α + χ b m.1 * β else 0) =
      (outZ D T a : ℝ) * α + (outZ D T b : ℝ) * β := by
  unfold outZ
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases m with ⟨i, j⟩
  unfold χ
  by_cases hj : j ∈ T
  · simp [hj]
  · by_cases hia : i = a
    · subst hia
      simp [hj, ha, hab]
    · by_cases hib : i = b
      · subst hib
        simp [hj, hb, hia]
      · simp [hj, hia, hib]

/-- The local formula: on the stencil box, the preactivation is the integer
`A(p)`, plus the local linear part, plus the pairs inside `T`. -/
theorem arg_pt (D : Descr N) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (hB : 2 ≤ B)
    {α β : ℝ} (hα : |α| ≤ 1) (hβ : |β| ≤ 1) :
    D.arg (pt T B a b α β) = (D.argZ (baseZ T B) : ℝ) + (vZ D T a : ℝ) * α +
      (vZ D T b : ℝ) * β + ∑ m in D.M, (if m.1 ∈ T ∧ m.2 ∈ T then
        relu (pt T B a b α β m.1 - pt T B a b α β m.2) else 0) := by
  rw [← Descr.arg_intCast]
  unfold Descr.arg
  have hpair : ∑ m in D.M, relu (pt T B a b α β m.1 - pt T B a b α β m.2) =
      ∑ m in D.M, (relu ((baseZ T B m.1 : ℝ) - baseZ T B m.2) +
        (if m.1 ∈ T ∧ m.2 ∉ T then χ a m.1 * α + χ b m.1 * β else 0) +
        (if m.1 ∈ T ∧ m.2 ∈ T then relu (pt T B a b α β m.1 - pt T B a b α β m.2) else 0)) :=
    Finset.sum_congr rfl fun m _ => relu_pt_split ha hb hab hB hα hβ m.1 m.2
  rw [sum_h_pt, hpair, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_out D ha hb hab]
  unfold vZ
  push_cast
  ring

/-- **Step 3.** If the functional does not vanish on a face function, then its
preactivation vanishes at the base point and it has a pair inside `T` or a
local head that is not a multiple of a root of `T`. -/
theorem pass_of_Λ_unit_ne (D : Descr N) {η : ℝ} (hη : 0 < η) (hη1 : 3 * η ≤ 1)
    (hB : 2 ≤ B) (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
    (hbd : 3 * η * (∑ o, |(D.h o : ℝ)| + 4 * D.M.card) ≤ 1)
    (hne : Λ T B a b η D.unit ≠ 0) :
    D.argZ (baseZ T B) = 0 ∧
      (PairIn D T ∨ (vZ D T a ≠ 0 ∧ vZ D T b ≠ 0 ∧ vZ D T a + vZ D T b ≠ 0)) := by
  have hbox : ∀ x : ℝ, |x| ≤ 3 * η → |x| ≤ 1 := fun x hx => le_trans hx hη1
  let P : ℝ → ℝ → ℝ := fun α β => ∑ m in D.M, (if m.1 ∈ T ∧ m.2 ∈ T then
    relu (pt T B a b α β m.1 - pt T B a b α β m.2) else 0)
  have hΛ : Λ T B a b η D.unit = Φ η (fun α β => relu ((D.argZ (baseZ T B) : ℝ) +
      (vZ D T a : ℝ) * α + (vZ D T b : ℝ) * β + P α β)) := by
    unfold Λ
    refine Φ_congr hη.le fun α β hα hβ => ?_
    unfold Descr.unit
    rw [arg_pt D ha hb hab hB (hbox α hα) (hbox β hβ)]
  have hP0 : Φ η P = 0 := by
    show Φ η (fun α β => ∑ m in D.M, (if m.1 ∈ T ∧ m.2 ∈ T then
      relu (pt T B a b α β m.1 - pt T B a b α β m.2) else 0)) = 0
    rw [Φ_sum]
    exact Finset.sum_eq_zero fun m _ => Φ_ite η _ _ fun _ =>
      Φ_relu_pt_pair hη.le hη1 hB ha hb hab m.1 m.2
  have hPnn : ∀ α β, 0 ≤ P α β := fun α β =>
    Finset.sum_nonneg fun m _ => by
      split_ifs
      · exact relu_nonneg _
      · exact le_refl 0
  have hPle : ∀ α β, |α| ≤ 3 * η → |β| ≤ 3 * η → P α β ≤ D.M.card * (6 * η) := by
    intro α β hα hβ
    calc P α β ≤ ∑ _m in D.M, 6 * η := Finset.sum_le_sum fun m _ => by
          split_ifs with h
          · have h1 := abs_pt_le (B := B) hab h.1 (by linarith) hα hβ
            have h2 := abs_pt_le (B := B) hab h.2 (by linarith) hα hβ
            have h3 : relu (pt T B a b α β m.1 - pt T B a b α β m.2) ≤
                |pt T B a b α β m.1 - pt T B a b α β m.2| :=
              max_le (abs_nonneg _) (le_abs_self _)
            linarith [abs_sub (pt T B a b α β m.1) (pt T B a b α β m.2)]
          · linarith
      _ = D.M.card * (6 * η) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hva : |(vZ D T a : ℝ)| ≤ |(D.h a : ℝ)| + D.M.card := by
    unfold vZ
    push_cast
    have h1 : (0 : ℝ) ≤ outZ D T a := by exact_mod_cast outZ_nonneg D T a
    have h2 : (outZ D T a : ℝ) ≤ D.M.card := by exact_mod_cast outZ_le D T a
    calc |(D.h a : ℝ) + outZ D T a| ≤ |(D.h a : ℝ)| + |(outZ D T a : ℝ)| := abs_add _ _
      _ ≤ _ := by rw [abs_of_nonneg h1]; linarith
  have hvb : |(vZ D T b : ℝ)| ≤ |(D.h b : ℝ)| + D.M.card := by
    unfold vZ
    push_cast
    have h1 : (0 : ℝ) ≤ outZ D T b := by exact_mod_cast outZ_nonneg D T b
    have h2 : (outZ D T b : ℝ) ≤ D.M.card := by exact_mod_cast outZ_le D T b
    calc |(D.h b : ℝ) + outZ D T b| ≤ |(D.h b : ℝ)| + |(outZ D T b : ℝ)| := abs_add _ _
      _ ≤ _ := by rw [abs_of_nonneg h1]; linarith
  have hhab : |(D.h a : ℝ)| + |(D.h b : ℝ)| ≤ ∑ o, |(D.h o : ℝ)| := by
    rw [← Finset.sum_pair (f := fun o => |(D.h o : ℝ)|) hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun o _ _ => abs_nonneg _
  have hsmall : 3 * η * (|(vZ D T a : ℝ)| + |(vZ D T b : ℝ)| + 2 * D.M.card) ≤ 1 := by
    refine le_trans ?_ hbd
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have hlin : ∀ α β, |α| ≤ 3 * η → |β| ≤ 3 * η →
      |(vZ D T a : ℝ) * α + (vZ D T b : ℝ) * β| ≤
        3 * η * (|(vZ D T a : ℝ)| + |(vZ D T b : ℝ)|) := by
    intro α β hα hβ
    calc |(vZ D T a : ℝ) * α + (vZ D T b : ℝ) * β|
        ≤ |(vZ D T a : ℝ)| * |α| + |(vZ D T b : ℝ)| * |β| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add _ _
      _ ≤ |(vZ D T a : ℝ)| * (3 * η) + |(vZ D T b : ℝ)| * (3 * η) :=
          add_le_add (mul_le_mul_of_nonneg_left hα (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hβ (abs_nonneg _))
      _ = _ := by ring
  have hcard : (0 : ℝ) ≤ D.M.card := Nat.cast_nonneg _
  by_contra hcon
  apply hne
  rw [hΛ]
  rcases (show 1 ≤ D.argZ (baseZ T B) ∨ D.argZ (baseZ T B) ≤ -1 ∨
      D.argZ (baseZ T B) = 0 by omega) with h1 | h1 | h1
  · have h1' : (1 : ℝ) ≤ D.argZ (baseZ T B) := by exact_mod_cast h1
    rw [Φ_congr hη.le (ψ := fun α β => ((D.argZ (baseZ T B) : ℝ) +
        (vZ D T a : ℝ) * α + (vZ D T b : ℝ) * β) + P α β)]
    · rw [Φ_add, Φ_affine, hP0, add_zero]
    · intro α β hα hβ
      apply relu_of_nonneg
      have := hlin α β hα hβ
      have := hPnn α β
      have := (abs_le.mp (hlin α β hα hβ)).1
      nlinarith [abs_nonneg (vZ D T a : ℝ), abs_nonneg (vZ D T b : ℝ)]
  · have h1' : (D.argZ (baseZ T B) : ℝ) ≤ -1 := by exact_mod_cast h1
    rw [Φ_congr hη.le (ψ := fun _ _ => 0)]
    · exact Φ_const η 0
    · intro α β hα hβ
      apply relu_of_nonpos
      have := (abs_le.mp (hlin α β hα hβ)).2
      have := hPle α β hα hβ
      nlinarith [abs_nonneg (vZ D T a : ℝ), abs_nonneg (vZ D T b : ℝ)]
  · have hnot : ¬ PairIn D T ∧
        ¬ (vZ D T a ≠ 0 ∧ vZ D T b ≠ 0 ∧ vZ D T a + vZ D T b ≠ 0) := by
      constructor
      · exact fun h => hcon ⟨h1, Or.inl h⟩
      · exact fun h => hcon ⟨h1, Or.inr h⟩
    have hP : ∀ α β, P α β = 0 := fun α β => Finset.sum_eq_zero fun m hm =>
      if_neg fun h => hnot.1 ⟨m, hm, h⟩
    rw [Φ_congr hη.le (ψ := fun α β => relu ((vZ D T a : ℝ) * α + (vZ D T b : ℝ) * β))]
    · apply Φ_relu_lin hη.le
      have h2 := hnot.2
      push_neg at h2
      by_cases hza : vZ D T a = 0
      · left; exact_mod_cast hza
      by_cases hzb : vZ D T b = 0
      · right; left; exact_mod_cast hzb
      right; right
      exact_mod_cast h2 hza hzb
    · intro α β _ _
      rw [hP, h1]
      push_cast
      ring_nf

end Units

end MaxCaterpillar.CountLower
