import Mathlib.Data.Real.Archimedean
import research.sN.exponential_push_20261102.ridge_annihilator.DifferenceAlgebra

/-! Research: finite differences are injective on functions whose support is
bounded in all coordinate contrasts. No continuity or compactness API is used. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.Ridge

variable {ι : Type*}

/-- The support is bounded after quotienting out simultaneous translation of
all coordinates. This formulation does not require a finite index type. -/
def ContrastBounded (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ i j, ∃ R : ℝ, ∀ x, R < |x i - x j| → f x = 0

theorem periodic_nat (f : (ι → ℝ) → ℝ) (v : ι → ℝ)
    (hp : ∀ x, f (x + v) = f x) (x : ι → ℝ) (n : ℕ) :
    f (fun i => x i + (n : ℝ) * v i) = f x := by
  induction n with
  | zero => simpa
  | succ n ih =>
    have he : (fun i => x i + ((n + 1 : ℕ) : ℝ) * v i) =
        (fun i => x i + (n : ℝ) * v i) + v := by
      funext i
      simp only [Nat.cast_add, Nat.cast_one, Pi.add_apply]
      ring
    rw [he, hp, ih]

theorem contrastBounded_periodic_eq_zero (f : (ι → ℝ) → ℝ)
    (hf : ContrastBounded f) (v : ι → ℝ)
    (hv : ∃ i j, v i ≠ v j) (hp : ∀ x, f (x + v) = f x) :
    f = 0 := by
  obtain ⟨i, j, hij⟩ := hv
  obtain ⟨R, hR⟩ := hf i j
  funext x
  have hd : 0 < |v i - v j| := abs_pos.mpr (sub_ne_zero.mpr hij)
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + |x i - x j|) / |v i - v j|)
  have hlarge : R + |x i - x j| < (n : ℝ) * |v i - v j| :=
    (div_lt_iff hd).mp hn
  have htri : (n : ℝ) * |v i - v j| ≤
      |(x i + (n : ℝ) * v i) - (x j + (n : ℝ) * v j)| +
      |x i - x j| := by
    calc
      (n : ℝ) * |v i - v j| = |(n : ℝ) * (v i - v j)| := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      _ = |((x i + (n : ℝ) * v i) - (x j + (n : ℝ) * v j)) -
          (x i - x j)| := by congr 1 <;> ring
      _ ≤ _ := abs_sub _ _
  have hz := hR (fun k => x k + (n : ℝ) * v k) (by linarith)
  have he := periodic_nat f v hp x n
  change f x = 0
  rw [← he, hz]

theorem contrastBounded_sub_translate (f : (ι → ℝ) → ℝ)
    (hf : ContrastBounded f) (v : ι → ℝ) :
    ContrastBounded (fun x => f (x + v) - f x) := by
  intro i j
  obtain ⟨R, hR⟩ := hf i j
  refine ⟨R + |v i - v j|, ?_⟩
  intro x hx
  have hzero : f x = 0 := hR x (by have := abs_nonneg (v i - v j); linarith)
  have htri : |x i - x j| ≤ |(x + v) i - (x + v) j| + |v i - v j| := by
    calc
      |x i - x j| = |((x + v) i - (x + v) j) - (v i - v j)| := by
        congr 1
        simp only [Pi.add_apply]
        ring
      _ ≤ _ := abs_sub _ _
  have hshift : f (x + v) = 0 := hR (x + v) (by linarith)
  change f (x + v) - f x = 0
  rw [hshift, hzero, sub_self]

theorem ContrastBounded.diff {f : (ι → ℝ) → ℝ}
    (hf : ContrastBounded f) (v : ι → ℝ) : ContrastBounded (diff v f) :=
  contrastBounded_sub_translate f hf v

theorem ContrastBounded.iterDiff {f : (ι → ℝ) → ℝ}
    (hf : ContrastBounded f) (vs : List (ι → ℝ)) : ContrastBounded (iterDiff vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact ih.diff v

/-- No non-diagonal translation difference can annihilate a function whose
support is bounded modulo the diagonal, unless the function already vanishes. -/
theorem diff_eq_zero_iff_of_contrastBounded (f : (ι → ℝ) → ℝ)
    (hf : ContrastBounded f) (v : ι → ℝ) (hv : ∃ i j, v i ≠ v j) :
    diff v f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply contrastBounded_periodic_eq_zero f hf v hv
    intro x
    have hx := congrFun h x
    change f (x + v) - f x = 0 at hx
    exact sub_eq_zero.mp hx
  · intro h
    rw [h, diff_zero]

/-- A finite product of such differences is still injective at zero. -/
theorem iterDiff_eq_zero_iff_of_contrastBounded (f : (ι → ℝ) → ℝ)
    (hf : ContrastBounded f) (vs : List (ι → ℝ))
    (hvs : ∀ v ∈ vs, ∃ i j, v i ≠ v j) :
    iterDiff vs f = 0 ↔ f = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [iterDiff_cons, diff_eq_zero_iff_of_contrastBounded _ (hf.iterDiff vs) v
      (hvs v (List.mem_cons_self v vs))]
    exact ih (fun w hw => hvs w (List.mem_cons_of_mem v hw))

#check @contrastBounded_periodic_eq_zero
#print axioms contrastBounded_periodic_eq_zero
#print axioms contrastBounded_sub_translate
#print axioms iterDiff_eq_zero_iff_of_contrastBounded
end MaxCaterpillar.ExponentialPush.Ridge
