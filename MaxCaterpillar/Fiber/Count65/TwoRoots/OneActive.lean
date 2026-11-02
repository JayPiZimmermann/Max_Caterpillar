import MaxCaterpillar.Fiber.Count65.TwoRoots.ForkFacets

/-! # A single active observation cannot retain a nonroot top-tie normal -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier BigOperators

/-- A row that retains a coordinate difference by itself must be that root.
This includes the nonzero coefficient conclusion. -/
theorem root_of_kernel_tie (a : Point 4) (i k : Fin 4) (hik : i ≠ k)
    (hker : ∀ w : Point 4, lin a w = 0 → w i = w k) :
    a i ≠ 0 ∧ ∀ l, a l = a i * ((if l = i then 1 else 0) -
      (if l = k then 1 else 0)) := by
  have hu (l : Fin 4) : lin a (unitVec l) = a l := by
    simp [lin,unitVec]
  have hai : a i ≠ 0 := by
    intro hz
    have hh := hker (unitVec i) (by rw [hu,hz])
    simpa [unitVec,Ne.symm hik] using hh
  refine ⟨hai,fun l => ?_⟩
  by_cases hli : l = i
  · subst l; simp [hik]
  have hh := hker (a i • unitVec l - a l • unitVec i) (by
    rw [lin_sub_right,lin_smul_right,lin_smul_right,hu,hu]; ring)
  by_cases hlk : l = k
  · subst l
    simp [Pi.sub_apply,Pi.smul_apply,unitVec,hik,Ne.symm hik] at hh
    simp [Ne.symm hik]
    linarith only [hh]
  · simp [Pi.sub_apply,Pi.smul_apply,unitVec,hli,hlk,Ne.symm hli,Ne.symm hlk,Ne.symm hik] at hh
    simpa [hli,hlk] using hh

/-- A nonzero nonroot row: no real scalar multiple of any coordinate
difference, including the zero scalar. Actual-network irredundancy separately
ensures that an invariant row cannot be zero. -/
def Nonroot (a : Point 4) : Prop :=
  ∀ i k : Fin 4, i ≠ k → ¬ ∃ c : ℝ,
    ∀ l, a l = c * ((if l = i then 1 else 0) - (if l = k then 1 else 0))

/-- A zero-sum nonroot cannot be supported on two coordinate positions. -/
theorem nonroot_not_supported_on_pair (a : Point 4) (hsum : ∑ l, a l = 0)
    (hs : Nonroot a) (i k : Fin 4) (hik : i ≠ k)
    (hout : ∀ l, l ≠ i → l ≠ k → a l = 0) : False := by
  classical
  have hpair : a i + a k = 0 := by
    calc
      a i + a k = ∑ l in ({i,k} : Finset (Fin 4)), a l := (Finset.sum_pair hik).symm
      _ = ∑ l, a l := Finset.sum_subset (Finset.subset_univ _) (by
        intro l _ hl
        apply hout l
        · intro hli; apply hl; simp [hli]
        · intro hlk; apply hl; simp [hlk])
      _ = 0 := hsum
  apply hs i k hik
  refine ⟨a i,fun l => ?_⟩
  by_cases hli : l = i
  · subst l; simp [hik]
  by_cases hlk : l = k
  · subst l
    simp only [Ne.symm hik,if_false,if_true,zero_sub,mul_neg,mul_one]
    linarith only [hpair]
  · simp [hli,hlk,hout l hli hlk]

/-- If all other rows are strictly negative at a top tie, an arbitrary
decoder cannot recover the target from a single nonroot row. -/
theorem not_one_active_nonroot (A : Fin 4 → Point 4) (h : Represents A)
    (q : Point 4) (i k p : Fin 4) (hik : i ≠ k)
    (hi : q i = Maximum 4 q) (hk : q k = Maximum 4 q)
    (hinactive : ∀ j, j ≠ p → lin (A j) q < 0)
    (hp : Nonroot (A p)) : False := by
  obtain ⟨ell,Phi,h⟩ := h
  have hker : ∀ w : Point 4, lin (A p) w = 0 → w i = w k := by
    intro w hw
    exact active_kernel_top_coordinates_eq A ell Phi h q w (fun j hj => by
      by_cases hjp : j = p
      · simpa [hjp] using hw
      · exact False.elim (not_lt_of_ge hj (hinactive j hjp))) i k hi hk
  exact hp i k hik ⟨(A p) i,(root_of_kernel_tie (A p) i k hik hker).2⟩

/-- With two possible nonroot observations at a top tie, each is forced
nonnegative. There is no generic-point or boundary omission. -/
theorem nonroot_nonneg_of_two_possible (A : Fin 4 → Point 4)
    (h : Represents A) (q : Point 4) (i k p r : Fin 4)
    (hik : i ≠ k) (hi : q i = Maximum 4 q) (hk : q k = Maximum 4 q)
    (hinactive : ∀ j, j ≠ p → j ≠ r → lin (A j) q < 0)
    (hr : Nonroot (A r)) : 0 ≤ lin (A p) q := by
  by_contra hh
  have hp : lin (A p) q < 0 := lt_of_not_ge hh
  apply not_one_active_nonroot A h q i k r hik hi hk _ hr
  intro j hjr
  by_cases hjp : j = p
  · simpa [hjp] using hp
  · exact hinactive j hjp hjr

/-- A row must be nonnegative if its removal would erase a target-tie
normal, even when other rows lie on their activation boundaries. -/
theorem row_nonneg_of_tie_kernel (A : Fin 4 → Point 4) (h : Represents A)
    (q w : Point 4) (i k p : Fin 4)
    (hi : q i = Maximum 4 q) (hk : q k = Maximum 4 q) (hne : w i ≠ w k)
    (hw : ∀ j, j ≠ p → 0 ≤ lin (A j) q → lin (A j) w = 0) :
    0 ≤ lin (A p) q := by
  obtain ⟨ell,Phi,h⟩ := h
  by_contra hh
  have hp : lin (A p) q < 0 := lt_of_not_ge hh
  apply hne
  exact active_kernel_top_coordinates_eq A ell Phi h q w (fun j hj => by
    by_cases hjp : j = p
    · subst j; exact False.elim (not_lt_of_ge hj hp)
    · exact hw j hjp hj) i k hi hk

#print axioms root_of_kernel_tie
#print axioms nonroot_nonneg_of_two_possible
end MaxCaterpillar.Fiber.Count65.TwoRoots
