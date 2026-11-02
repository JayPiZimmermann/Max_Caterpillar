import MaxCaterpillar.Fiber.First65.ActiveSpan
import MaxCaterpillar.Frontier.Constructions

/-! # Width-independent necessary inequalities for the inward two-root fork

The decoder is arbitrary. The inequalities come directly from information loss
on two actual top-tie facets, rather than any restriction on second-layer gates.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier
open BigOperators

@[simp] lemma vec_four_three {X : Type*} (a b c d : X) :
    (![a,b,c,d] : Fin 4 → X) 3 = d := rfl

noncomputable def forkRows (α β κ : ℝ) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![0,-1,1,0],
    ![-α,α+β-1,-β,1], ![-α,α+β-κ,-β,κ]]

/-- The actual factorization assertion, without any gate-count hypothesis. -/
def Represents (A : Fin 4 → Point 4) : Prop :=
  ∃ ell : Point 4, ∃ Phi : (Fin 4 → ℝ) → ℝ,
    ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x))

lemma lin_four (a x : Point 4) : lin a x =
    a 0*x 0+a 1*x 1+a 2*x 2+a 3*x 3 := by
  simp [lin, Fin.sum_univ_succ, add_assoc,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide]

/-- The positive `x0=x3` facet forces the second nonroot's coefficient
of `x3-x1` to be at least the first nonroot's `x0-x1` coefficient. -/
theorem fork_kappa_ge_alpha {α β κ : ℝ} (hβ : 0 < β)
    (h : Represents (forkRows α β κ)) : α ≤ κ := by
  obtain ⟨ell, Phi, h⟩ := h
  by_contra hh
  have hκα : κ-α < 0 := sub_neg.mpr (lt_of_not_ge hh)
  let q : Point 4 := ![β,0,(κ-α)/2,β]
  let w : Point 4 := ![0,0,1,β]
  have hs : lin (forkRows α β κ 3) q < 0 := by
    norm_num [lin_four, forkRows, q]
    nlinarith only [mul_neg_of_pos_of_neg hβ hκα]
  have hq : q 0 = Maximum 4 q := by
    rw [Maximum_four]
    change β = max (max β 0) (max ((κ-α)/2) β)
    rw [show max β 0 = β from max_eq_left hβ.le,
      show max ((κ-α)/2) β = β from max_eq_right (by linarith only [hβ,hκα]),max_self]
  have hq3 : q 3 = Maximum 4 q := by exact hq
  have he := active_kernel_top_coordinates_eq (forkRows α β κ) ell Phi h q w
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four, forkRows, w]
      · have hn : lin (forkRows α β κ 1) q < 0 := by
          rw [lin_four]
          change 0 * β + -1 * 0 + 1 * ((κ-α)/2) + 0 * β < 0
          linarith only [hκα]
        exact False.elim (not_lt_of_ge hj hn)
      · norm_num [lin_four, forkRows, w]
      · exact False.elim (not_lt_of_ge hj hs)) 0 3 hq hq3
  have : (0 : ℝ) = β := by exact he
  linarith only [this,hβ]

/-- The symmetric positive `x2=x3` facet gives the other coefficient bound. -/
theorem fork_kappa_ge_beta {α β κ : ℝ} (hα : 0 < α)
    (h : Represents (forkRows α β κ)) : β ≤ κ := by
  obtain ⟨ell, Phi, h⟩ := h
  by_contra hh
  have hκβ : κ-β < 0 := sub_neg.mpr (lt_of_not_ge hh)
  let q : Point 4 := ![(κ-β)/2,0,α,α]
  let w : Point 4 := ![1,0,0,α]
  have hs : lin (forkRows α β κ 3) q < 0 := by
    norm_num [lin_four, forkRows, q]
    nlinarith only [mul_neg_of_pos_of_neg hα hκβ]
  have hq : q 2 = Maximum 4 q := by
    rw [Maximum_four]
    change α = max (max ((κ-β)/2) 0) (max α α)
    rw [show max ((κ-β)/2) 0 = 0 from max_eq_right (by linarith only [hκβ]),
      max_self,show max 0 α = α from max_eq_right hα.le]
  have hq3 : q 3 = Maximum 4 q := by exact hq
  have he := active_kernel_top_coordinates_eq (forkRows α β κ) ell Phi h q w
    (fun j hj => by
      fin_cases j
      · have hn : lin (forkRows α β κ 0) q < 0 := by
          rw [lin_four]
          change 1 * ((κ-β)/2) + -1 * 0 + 0 * α + 0 * α < 0
          linarith only [hκβ]
        exact False.elim (not_lt_of_ge hj hn)
      · norm_num [lin_four, forkRows, w]
      · norm_num [lin_four, forkRows, w]
      · exact False.elim (not_lt_of_ge hj hs)) 2 3 hq hq3
  have : (0 : ℝ) = α := by exact he
  linarith only [this,hα]

/-- Both necessary inequalities, with all real coefficients unrestricted. -/
theorem fork_facet_bounds {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (h : Represents (forkRows α β κ)) : max α β ≤ κ ∧ 0 < κ := by
  have ha := fork_kappa_ge_alpha hβ h
  have hb := fork_kappa_ge_beta hα h
  exact ⟨max_le ha hb, lt_of_lt_of_le hα ha⟩

#print axioms fork_facet_bounds
end MaxCaterpillar.Fiber.Count65.TwoRoots
