import MaxCaterpillar.CountLower.Keys
import MaxCaterpillar.Compilation

/-! # A lower bound on the number of caterpillar face functions

Any expansion of the maximum of `N = r + 2` coordinates by normalized
caterpillar face functions `K` and an auxiliary remainder (a linear combination
of the neurons of the first hidden layer) uses `|K| ≥ N(N-1)/6` face functions.

For each three-set `T` of coordinates, the six-point functional `Λ` of
`CountLower/Functional.lean` kills the auxiliary span and takes the value
`2η ≠ 0` on the maximum, so some face function of `K` is not killed.  By steps
3–5 such a face function admits `T`, and each face function admits at most
`N - 2` three-sets.  Hence `C(N,3) ≤ |K| (N - 2)`.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar MaxNN.Width CountLower

namespace Trees

/-! ## One count for all functions with a good description -/

/-- `C(N,3) ≤ |K| (N - 2)` for every expansion by functions with a `Good` description. -/
theorem choose_three_le_of_good (r : ℕ) {ι : Type*} (K : Finset ι)
    (U : ι → (Fin (r + 1 + 1) → ℝ) → ℝ)
    (hU : ∀ i ∈ K, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, U i y = D.unit y)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * U k x + auxiliary a x) :
    (r + 1 + 1).choose 3 ≤ K.card * r := by
  classical
  haveI : Inhabited (Descr (r + 1 + 1)) := ⟨⟨0, ∅⟩⟩
  choose! D apex hgood hunit using hU
  let B : ℕ := 2 + ∑ k in K, (∑ o, ((D k).h o).natAbs + (D k).M.card)
  let S : ℝ := ∑ k in K, (∑ o, |((D k).h o : ℝ)| + 4 * (D k).M.card)
  let η : ℝ := 1 / (3 * (1 + S))
  have hSk : ∀ k ∈ K, 0 ≤ ∑ o, |((D k).h o : ℝ)| + 4 * ((D k).M.card : ℝ) := fun k _ =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _) (by positivity)
  have hS0 : 0 ≤ S := Finset.sum_nonneg hSk
  have hη : 0 < η := by positivity
  have hη3 : 3 * η = 1 / (1 + S) := by
    show (3 : ℝ) * (1 / (3 * (1 + S))) = 1 / (1 + S)
    rw [mul_one_div, ← div_div, div_self (by norm_num : (3 : ℝ) ≠ 0)]
  have hη1 : 3 * η ≤ 1 := by
    rw [hη3, div_le_one (by linarith)]
    linarith
  have hB2 : 2 ≤ B := Nat.le_add_right 2 _
  have hBk : ∀ k ∈ K, ∑ o, |(D k).h o| + ((D k).M.card : ℤ) < (B : ℤ) := by
    intro k hk
    have h1 : ∑ o, |(D k).h o| + ((D k).M.card : ℤ) =
        ((∑ o, ((D k).h o).natAbs + (D k).M.card : ℕ) : ℤ) := by
      push_cast
      simp only [Int.coe_natAbs]
    have h2 : ∑ o, ((D k).h o).natAbs + (D k).M.card ≤
        ∑ k in K, (∑ o, ((D k).h o).natAbs + (D k).M.card) :=
      Finset.single_le_sum (f := fun k => ∑ o, ((D k).h o).natAbs + (D k).M.card)
        (fun _ _ => Nat.zero_le _) hk
    rw [h1]
    have : ∑ o, ((D k).h o).natAbs + (D k).M.card < B := by
      simp only [B]
      omega
    exact_mod_cast this
  have hbdk : ∀ k ∈ K,
      3 * η * (∑ o, |((D k).h o : ℝ)| + 4 * (D k).M.card) ≤ 1 := by
    intro k hk
    have h1 : ∑ o, |((D k).h o : ℝ)| + 4 * ((D k).M.card : ℝ) ≤ S :=
      Finset.single_le_sum (f := fun k => ∑ o, |((D k).h o : ℝ)| + 4 * ((D k).M.card : ℝ))
        hSk hk
    rw [hη3, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  have hcover : Finset.powersetCard 3 (Finset.univ : Finset (Fin (r + 1 + 1))) ⊆
      K.biUnion fun k => allowed (D k) (apex k) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨p, q, c, hpq, hpc, hqc, hTe⟩ := Finset.card_eq_three.mp hT.2
    have hp : p ∈ T := by rw [hTe]; simp
    have hq : q ∈ T := by rw [hTe]; simp
    have hc : c ∈ T := by rw [hTe]; simp
    have hsplit : Λ T B p q η (MAX (r + 1 + 1)) =
        ∑ k in K, d k * Λ T B p q η (U k) +
          Λ T B p q η (fun x => ∑ j, a j * feat (r + 1 + 1) x j) := by
      unfold Λ
      have e : (fun α β => MAX (r + 1 + 1) (pt T B p q α β)) = fun α β =>
          (∑ k in K, (fun k α β => d k * U k (pt T B p q α β)) k α β) +
            (fun x => ∑ j, a j * feat (r + 1 + 1) x j) (pt T B p q α β) := by
        funext α β
        exact h _
      rw [e, Φ_add, Φ_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => Φ_mul η (d k) _
    rw [Λ_MAX hη.le hp hq hc hpq (Ne.symm hpc) (Ne.symm hqc),
      Λ_auxiliary hη.le hη1 hB2 hp hq hpq, add_zero] at hsplit
    have hne : ∑ k in K, d k * Λ T B p q η (U k) ≠ 0 := by
      rw [← hsplit]
      exact (mul_pos two_pos hη).ne'
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hUk : Λ T B p q η (D k).unit ≠ 0 := by
      have e : U k = (D k).unit := funext (hunit k hk)
      rw [← e]
      exact right_ne_zero_of_mul hk0
    have hpass := pass_of_Λ_unit_ne (D k) hη hη1 hB2 hp hq hpq (hbdk k hk) hUk
    exact Finset.mem_biUnion.mpr
      ⟨k, hk, mem_allowed (hgood k hk) hTe hpq hpc hqc (hBk k hk) hpass⟩
  have h1 := Finset.card_le_of_subset hcover
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
  calc (r + 1 + 1).choose 3 ≤ (K.biUnion fun k => allowed (D k) (apex k)).card := h1
    _ ≤ ∑ k in K, (allowed (D k) (apex k)).card := Finset.card_biUnion_le
    _ ≤ ∑ _k in K, r := Finset.sum_le_sum fun k hk => by
        have := card_allowed (hgood k hk)
        simpa using this
    _ = K.card * r := by rw [Finset.sum_const, smul_eq_mul]

/-- `N(N-1) ≤ 6|K|` for every expansion by functions with a `Good` description. -/
theorem count_lower_of_good (r : ℕ) (hr : 1 ≤ r) {ι : Type*} (K : Finset ι)
    (U : ι → (Fin (r + 1 + 1) → ℝ) → ℝ)
    (hU : ∀ i ∈ K, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, U i y = D.unit y)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * U k x + auxiliary a x) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card := by
  have h3 := choose_three_le_of_good r K U hU d a h
  have hdesc : (r + 1 + 1).descFactorial 3 = (r + 1 + 1) * (r + 1) * r := by
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_one]
    ring
  have hfac : (r + 1 + 1).descFactorial 3 = 6 * (r + 1 + 1).choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h6 : (r + 1 + 1) * (r + 1) * r ≤ 6 * K.card * r := by
    rw [← hdesc, hfac, mul_assoc]
    exact Nat.mul_le_mul_left 6 h3
  exact le_of_mul_le_mul_right h6 (by omega)

end Trees

/-- The count with three-sets: `C(N,3) ≤ |K| (N - 2)` for `N = r + 2`. -/
theorem caterpillar_choose_three_le (r : ℕ)
    (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x) :
    (r + 1 + 1).choose 3 ≤ K.card * r := by
  exact Trees.choose_three_le_of_good r K Caterpillar.Corrections.realUnitY
    (fun k hk => exists_descr (hK hk)) d a h

/-- **Lower bound on the number of face functions.** Any expansion of the
maximum of `N = r + 2` coordinates by normalized caterpillar face functions
`K`, with an auxiliary remainder, satisfies `N (N - 1) ≤ 6 |K|`. -/
theorem caterpillar_count_lower (r : ℕ) (hr : 1 ≤ r)
    (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card := by
  exact Trees.count_lower_of_good r hr K Caterpillar.Corrections.realUnitY
    (fun k hk => exists_descr (hK hk)) d a h

end MaxCaterpillar
