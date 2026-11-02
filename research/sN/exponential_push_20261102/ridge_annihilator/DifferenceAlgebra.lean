import Mathlib.Tactic

/-! Research-only algebra of exact translation differences. -/
set_option autoImplicit false

namespace MaxCaterpillar.ExponentialPush.Ridge

open BigOperators

variable {E : Type*} [AddCommGroup E]

/-- Forward difference by a fixed translation. -/
def diff (v : E) (f : E → ℝ) : E → ℝ := fun x => f (x + v) - f x

/-- The finite product of commuting translation differences. -/
def iterDiff : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: vs, f => diff v (iterDiff vs f)

@[simp] theorem iterDiff_nil (f : E → ℝ) : iterDiff [] f = f := rfl

@[simp] theorem iterDiff_cons (v : E) (vs : List E) (f : E → ℝ) :
    iterDiff (v :: vs) f = diff v (iterDiff vs f) := rfl

@[simp] theorem diff_zero (v : E) : diff v (0 : E → ℝ) = 0 := by
  funext x
  simp [diff]

@[simp] theorem iterDiff_zero (vs : List E) : iterDiff vs (0 : E → ℝ) = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [iterDiff_cons, ih, diff_zero]

theorem diff_add (v : E) (f g : E → ℝ) :
    diff v (f + g) = diff v f + diff v g := by
  funext x
  simp only [diff, Pi.add_apply]
  ring

theorem diff_sub (v : E) (f g : E → ℝ) :
    diff v (f - g) = diff v f - diff v g := by
  funext x
  simp only [diff, Pi.sub_apply]
  ring

theorem diff_mul (v : E) (a : ℝ) (f : E → ℝ) :
    diff v (fun x => a * f x) = fun x => a * diff v f x := by
  funext x
  simp only [diff]
  ring

theorem diff_translate (v u : E) (f : E → ℝ) :
    diff v (fun x => f (x + u)) = fun x => diff v f (x + u) := by
  funext x
  simp only [diff]
  congr 2
  ac_rfl

theorem diff_comm (u v : E) (f : E → ℝ) :
    diff u (diff v f) = diff v (diff u f) := by
  funext x
  simp only [diff]
  have h : x + u + v = x + v + u := by ac_rfl
  rw [h]
  ring

theorem iterDiff_add (vs : List E) (f g : E → ℝ) :
    iterDiff vs (f + g) = iterDiff vs f + iterDiff vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [iterDiff_cons, ih, diff_add]; rfl

theorem iterDiff_sub (vs : List E) (f g : E → ℝ) :
    iterDiff vs (f - g) = iterDiff vs f - iterDiff vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [iterDiff_cons, ih, diff_sub]; rfl

theorem iterDiff_mul (vs : List E) (a : ℝ) (f : E → ℝ) :
    iterDiff vs (fun x => a * f x) = fun x => a * iterDiff vs f x := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [iterDiff_cons, ih, diff_mul]; rfl

theorem iterDiff_translate (vs : List E) (u : E) (f : E → ℝ) :
    iterDiff vs (fun x => f (x + u)) = fun x => iterDiff vs f (x + u) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [iterDiff_cons, ih, diff_translate]; rfl

theorem iterDiff_diff (vs : List E) (v : E) (f : E → ℝ) :
    iterDiff vs (diff v f) = diff v (iterDiff vs f) := by
  induction vs with
  | nil => rfl
  | cons u us ih => rw [iterDiff_cons, ih, diff_comm]; rfl

theorem iterDiff_comm (vs ws : List E) (f : E → ℝ) :
    iterDiff vs (iterDiff ws f) = iterDiff ws (iterDiff vs f) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [iterDiff_cons, iterDiff_diff, ih]; rfl

theorem iterDiff_append (vs ws : List E) (f : E → ℝ) :
    iterDiff (vs ++ ws) f = iterDiff vs (iterDiff ws f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append, iterDiff_cons, ih]

theorem iterDiff_sum {ι : Type*} (vs : List E) (s : Finset ι) (f : ι → E → ℝ) :
    iterDiff vs (∑ i in s, f i) = ∑ i in s, iterDiff vs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, iterDiff_add, ih, Finset.sum_insert hi]

/-- Exact commutation with any finite weighted sum of translates. -/
theorem iterDiff_weighted_translate {ι : Type*} (vs : List E)
    (s : Finset ι) (a : ι → ℝ) (u : ι → E) (f : E → ℝ) :
    iterDiff vs (fun x => ∑ i in s, a i * f (x + u i)) =
      fun x => ∑ i in s, a i * iterDiff vs f (x + u i) := by
  have he : (fun x => ∑ i in s, a i * f (x + u i)) =
      ∑ i in s, fun x => a i * f (x + u i) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he, iterDiff_sum]
  funext x
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iterDiff_mul, iterDiff_translate]

/-- An invariant direction anywhere in the list annihilates the function. -/
theorem iterDiff_eq_zero_of_mem_invariant (vs : List E) (v : E) (f : E → ℝ)
    (hv : v ∈ vs) (hf : ∀ x, f (x + v) = f x) : iterDiff vs f = 0 := by
  have hd : diff v f = 0 := by
    funext x
    simp only [diff, hf, sub_self, Pi.zero_apply]
  induction vs with
  | nil => simp at hv
  | cons u us ih =>
    rcases List.mem_cons.mp hv with h | h
    · subst u
      rw [iterDiff_cons, ← iterDiff_diff, hd, iterDiff_zero]
    · rw [iterDiff_cons, ih h, diff_zero]

/-- One invariant direction for each summand gives a common annihilator. -/
theorem iterDiff_sum_eq_zero {ι : Type*} (vs : List E) (s : Finset ι)
    (v : ι → E) (f : ι → E → ℝ)
    (hmem : ∀ i ∈ s, v i ∈ vs)
    (hinv : ∀ i ∈ s, ∀ x, f i (x + v i) = f i x) :
    iterDiff vs (∑ i in s, f i) = 0 := by
  rw [iterDiff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact iterDiff_eq_zero_of_mem_invariant vs (v i) (f i) (hmem i hi) (hinv i hi)

/-- Two exact differences annihilate every affine function. -/
theorem diff_diff_affine (u v : E) (a : E →+ ℝ) (c : ℝ) :
    diff u (diff v (fun x => a x + c)) = 0 := by
  funext x
  simp only [diff, map_add, Pi.zero_apply]
  ring

theorem iterDiff_affine_of_two (u v : E) (vs : List E) (a : E →+ ℝ) (c : ℝ) :
    iterDiff (u :: v :: vs) (fun x => a x + c) = 0 := by
  change diff u (diff v (iterDiff vs (fun x => a x + c))) = 0
  rw [← iterDiff_diff, ← iterDiff_diff, diff_diff_affine, iterDiff_zero]

#print axioms iterDiff_weighted_translate
#print axioms iterDiff_sum_eq_zero

end MaxCaterpillar.ExponentialPush.Ridge
