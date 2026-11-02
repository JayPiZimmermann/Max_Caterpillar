import MaxCaterpillar.Frontier.RandomRestriction.CartesianRaw

/-! # Actual Cartesian gap points and their real polynomials

The two permutations remain the original tail-label order and distinct gap-rank
order. Arbitrary real weights give an exact suffix-coefficient expansion, with
no zero-sum or survival hypothesis. The zero-sum condition is used only when
rewriting suffix coefficients in the source prefix convention.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Cartesian
open BigOperators

/-- The anchor is zero, and every tail coordinate is the negative cumulative
sum of actual gap powers up to its position in the original label order. -/
noncomputable def gapPoint {m : ℕ} (p : RawConfig m) (T : ℝ) : Option (Fin m)→ℝ
  | none => 0
  | some a => -∑ g in Finset.univ.filter (fun g : Fin m => g.val≤(p.1.symm a).val),
      T^((p.2 g).val)

/-- The coefficient of the original gap at position g is a negative suffix sum. -/
noncomputable def tailCoefficient {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (g : Fin m) : ℝ :=
  -∑ k in Finset.univ.filter (fun k : Fin m => g.val≤k.val),w (some (p.1 k))

/-- Expanding the actual point gives the gap polynomial without any condition
on the anchor coefficient or on the sum of the weights. -/
theorem weighted_gapPoint_eq_sum {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (T : ℝ) :
    (∑ x : Option (Fin m),w x*gapPoint p T x)=
      ∑ g : Fin m,tailCoefficient p w g*T^((p.2 g).val) := by
  classical
  have ht := Equiv.sum_comp p.1 (fun a => w (some a)*gapPoint p T (some a))
  simp only [gapPoint,Equiv.symm_apply_apply] at ht
  calc
    _ = ∑ k : Fin m,w (some (p.1 k)) *
        (-∑ g in Finset.univ.filter (fun g : Fin m => g.val≤k.val),T^((p.2 g).val)) := by
      rw [Fintype.sum_option]
      simp only [gapPoint,mul_zero,zero_add]
      exact ht.symm
    _ = ∑ k : Fin m,∑ g in Finset.univ.filter (fun g : Fin m => g.val≤k.val),
        (-w (some (p.1 k)))*T^((p.2 g).val) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
      ring
    _ = ∑ k : Fin m,∑ g : Fin m,
        if g.val≤k.val then (-w (some (p.1 k)))*T^((p.2 g).val) else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑ g : Fin m,∑ k : Fin m,
        if g.val≤k.val then (-w (some (p.1 k)))*T^((p.2 g).val) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      unfold tailCoefficient
      rw [Finset.sum_filter,neg_mul,Finset.sum_mul,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring

/-- Vanishing suffix sums force every tail entry to vanish. The maximal
nonzero support index provides one triangular elimination step; the argument
also covers an empty tail. -/
theorem tailCoefficient_all_zero_iff {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) :
    (∀ g : Fin m,tailCoefficient p w g=0) ↔ ∀ a : Fin m,w (some a)=0 := by
  classical
  constructor
  · intro H a
    by_contra ha
    let S : Finset (Fin m) := Finset.univ.filter (fun k => w (some (p.1 k))≠0)
    have hS : S.Nonempty := ⟨p.1.symm a,by simpa only
      [S,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.apply_symm_apply] using ha⟩
    let g : Fin m := S.max' hS
    have hg : g∈S := Finset.max'_mem S hS
    have hwg : w (some (p.1 g))≠0 := (Finset.mem_filter.mp hg).2
    have hs : (∑ k in Finset.univ.filter (fun k : Fin m => g.val≤k.val),
        w (some (p.1 k)))=w (some (p.1 g)) := by
      apply Finset.sum_eq_single g
      · intro k hk hkg
        by_contra hk0
        have hkS : k∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk0⟩
        have hle : k.val≤g.val := Finset.le_max' S k hkS
        have hge : g.val≤k.val := (Finset.mem_filter.mp hk).2
        exact hkg (Fin.ext (Nat.le_antisymm hle hge))
      · intro hn
        exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩))
    have he := H g
    unfold tailCoefficient at he
    rw [hs] at he
    exact hwg (neg_eq_zero.mp he)
  · intro H g
    simp only [tailCoefficient,H,Finset.sum_const_zero,neg_zero]

/-- Under the full anchor-plus-tail zero-sum relation, the exact negative
suffix coefficient is the anchor plus the strict prefix in the original order. -/
theorem tailCoefficient_eq_prefix {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (hzero : (∑ x : Option (Fin m),w x)=0) (g : Fin m) :
    tailCoefficient p w g=w none+
      ∑ k in Finset.univ.filter (fun k : Fin m => k.val<g.val),w (some (p.1 k)) := by
  classical
  have ht : w none+(∑ k : Fin m,w (some (p.1 k)))=0 := by
    rw [Equiv.sum_comp p.1 (fun a => w (some a))]
    simpa only [Fintype.sum_option] using hzero
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m))
    (fun k => k.val<g.val) (fun k => w (some (p.1 k)))
  simp only [not_lt] at hs
  unfold tailCoefficient
  linarith only [ht,hs]

/-- The actual real polynomial, whose exponents are the distinct original rho ranks. -/
noncomputable def gapPolynomial {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) : Polynomial ℝ :=
  ∑ g : Fin m,Polynomial.monomial ((p.2 g).val) (tailCoefficient p w g)

theorem gapPolynomial_eval {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (T : ℝ) :
    (gapPolynomial p w).eval T=∑ x : Option (Fin m),w x*gapPoint p T x := by
  rw [gapPolynomial,Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  exact (weighted_gapPoint_eq_sum p w T).symm

/-- A coefficient at an actual rho rank is exactly its original suffix coefficient. -/
theorem gapPolynomial_coeff_rank {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (g : Fin m) :
    (gapPolynomial p w).coeff ((p.2 g).val)=tailCoefficient p w g := by
  classical
  unfold gapPolynomial
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single g]
  · rw [Polynomial.coeff_monomial,if_pos rfl]
  · intro k _ hkg
    have he : (p.2 k).val≠(p.2 g).val := by
      intro hh
      exact hkg (p.2.injective (Fin.ext hh))
    simp only [Polynomial.coeff_monomial,if_neg he]
  · intro hn
    exact False.elim (hn (Finset.mem_univ g))

/-- Distinct gap ranks prevent cancellation: the actual polynomial vanishes
exactly when every tail weight vanishes, regardless of the anchor weight. -/
theorem gapPolynomial_eq_zero_iff {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) : gapPolynomial p w=0 ↔ ∀ a : Fin m,w (some a)=0 := by
  constructor
  · intro H
    apply (tailCoefficient_all_zero_iff p w).mp
    intro g
    have he := congrArg (fun f : Polynomial ℝ => f.coeff ((p.2 g).val)) H
    simpa only [gapPolynomial_coeff_rank,Polynomial.coeff_zero] using he
  · intro H
    have hc := (tailCoefficient_all_zero_iff p w).mpr H
    simp only [gapPolynomial,hc,map_zero,Finset.sum_const_zero]

/-- On the actual zero-sum weight space, the gap polynomial is faithful to
all original coefficients, including the anchor. -/
theorem gapPolynomial_eq_zero_iff_of_zeroSum {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (hzero : (∑ x : Option (Fin m),w x)=0) :
    gapPolynomial p w=0 ↔ ∀ x : Option (Fin m),w x=0 := by
  constructor
  · intro H
    have ht := (gapPolynomial_eq_zero_iff p w).mp H
    have ha : w none=0 := by
      simpa only [Fintype.sum_option,ht,Finset.sum_const_zero,add_zero] using hzero
    intro x
    cases x with
    | none => exact ha
    | some a => exact ht a
  · intro H
    exact (gapPolynomial_eq_zero_iff p w).mpr (fun a => H (some a))
end MaxCaterpillar.Frontier.RandomRestriction.Cartesian
