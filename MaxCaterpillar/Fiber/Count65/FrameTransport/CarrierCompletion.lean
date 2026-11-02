import MaxCaterpillar.Fiber.Count65.CarrierAxis

/-! # Completing an actual four-invariant frame by its two coordinate carriers

The carrier rows are extracted from the actual six-row first matrix. Their
coordinate directions follow from one input where all invariant rows are
strictly inactive. No carrier-axis or full-matrix normal form is assumed.
Original biases and the second hidden width are unrestricted.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators

lemma row_eq_sum_smul_unitVec {N : ℕ} (a : Point N) (i : Fin N)
    (hsupport : ∀ k, k ≠ i → a k = 0) :
    a = (∑ k, a k) • unitVec i := by
  classical
  have hsum : (∑ k, a k) = a i := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact hsupport k hki
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  funext k
  by_cases hki : k = i
  · subst k
    simp [Pi.smul_apply,unitVec,hsum]
  · simp [Pi.smul_apply,unitVec,hki,hsupport k hki]

/-- The two noninvariant rows have unique opposite slope signs. This is
extracted from the actual network, not stipulated by a frame definition. -/
theorem unique_carriers_of_four_invariants {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ k, net.W₁ j k) = 0).card = 4) :
    ∃ pplus pminus : Fin 6,
      pplus ≠ pminus ∧
      0 < ∑ k, net.W₁ pplus k ∧ (∑ k, net.W₁ pminus k) < 0 ∧
      (∀ j, 0 < ∑ k, net.W₁ j k → j = pplus) ∧
      (∀ j, (∑ k, net.W₁ j k) < 0 → j = pminus) ∧
      (∀ j, (∑ k, net.W₁ j k) = 0 ↔ j ≠ pplus ∧ j ≠ pminus) := by
  obtain ⟨p,n,c,hpn,_hc,hp,hn,_hprop,hother⟩ :=
    max4_four_invariant_rows_have_opposite_carriers net hnet hcard
  have hpos : ∀ j, 0 < ∑ k, net.W₁ j k → j = p := by
    intro j hj
    by_contra hjp
    by_cases hjn : j = n
    · subst j
      linarith only [hj,hn]
    · have hz := hother j hjp hjn
      linarith only [hj,hz]
  have hneg : ∀ j, (∑ k, net.W₁ j k) < 0 → j = n := by
    intro j hj
    by_contra hjn
    by_cases hjp : j = p
    · subst j
      linarith only [hj,hp]
    · have hz := hother j hjp hjn
      linarith only [hj,hz]
  refine ⟨p,n,hpn,hp,hn,hpos,hneg,fun j => ?_⟩
  constructor
  · intro hz
    constructor
    · intro hjp
      subst j
      linarith only [hp,hz]
    · intro hjn
      subst j
      linarith only [hn,hz]
  · rintro ⟨hjp,hjn⟩
    exact hother j hjp hjn

/-- One strict-inactive invariant state forces the two remaining actual
first-layer rows to be positive multiples of the winning coordinate and its
negative. The final iff identifies exactly the other four physical rows. -/
theorem coordinate_carrier_completion {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ k, net.W₁ j k) = 0).card = 4)
    (i : Fin 4) (q : Point 4) (hq : q i = Maximum 4 q)
    (hinactive : ∀ j, (∑ k, net.W₁ j k) = 0 → lin (net.W₁ j) q < 0) :
    ∃ pplus pminus : Fin 6, ∃ cp cm : ℝ,
      pplus ≠ pminus ∧ 0 < cp ∧ 0 < cm ∧
      net.W₁ pplus = cp • unitVec i ∧
      net.W₁ pminus = cm • (-unitVec i) ∧
      (∀ j, (∑ k, net.W₁ j k) = 0 ↔ j ≠ pplus ∧ j ≠ pminus) := by
  obtain ⟨p,n,hpn,hp,hn,hpos,hneg,hother⟩ :=
    unique_carriers_of_four_invariants net hnet hcard
  have hpaxis := positive_carrier_axis_of_inactive_invariants net hnet p i q hq hpos hinactive
  have hnaxis := negative_carrier_axis_of_inactive_invariants net hnet n i q hq hneg hinactive
  refine ⟨p,n,∑ k, net.W₁ p k,-(∑ k, net.W₁ n k),hpn,hp,
    neg_pos.mpr hn,row_eq_sum_smul_unitVec _ i hpaxis,?_,hother⟩
  calc
    net.W₁ n = (∑ k, net.W₁ n k) • unitVec i :=
      row_eq_sum_smul_unitVec _ i hnaxis
    _ = -(∑ k, net.W₁ n k) • (-unitVec i) := by
      funext k
      simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul,neg_mul_neg]

#print axioms unique_carriers_of_four_invariants
#print axioms coordinate_carrier_completion
end MaxCaterpillar.Fiber.Count65.FrameTransport
