import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-! Exact coin columns for all parallel real first-layer rows. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators
open NormalizedNetwork
variable {N h₁ h₂ : ℕ}

/-- The oriented coordinate root. -/
noncomputable def braidRoot (a b : Fin N) : Point N := unitVec a - unitVec b

/-- Change of the active indicator when the endpoint order is exchanged. -/
noncomputable def edgeCoinDifference (A : Point N) (a b : Fin N) : ℝ :=
  (if 0 < A a then 1 else 0) - (if 0 < A b then 1 else 0)

theorem row_zero_off_pair (A : Point N) (a b : Fin N)
    (hsupp : rowSupport A ⊆ {a,b}) (i : Fin N) (hia : i ≠ a) (hib : i ≠ b) :
    A i = 0 := by
  by_contra hi
  have := hsupp ((mem_rowSupport A i).mpr hi)
  simpa [Finset.mem_insert,Finset.mem_singleton,hia,hib] using this

theorem row_other_endpoint (A : Point N) (a b : Fin N) (hab : a ≠ b)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {a,b}) : A b = - A a := by
  have hp : A a + A b = 0 := by
    calc
      A a + A b = ∑ i in ({a,b} : Finset (Fin N)), A i := (Finset.sum_pair hab).symm
      _ = ∑ i, A i := Finset.sum_subset (Finset.subset_univ _) (by
        intro i _ hi
        apply row_zero_off_pair A a b hsupp i
        · intro h; exact hi (by simp [h])
        · intro h; exact hi (by simp [h]))
      _ = 0 := hsum
  linarith

theorem row_eq_root_smul (A : Point N) (a b : Fin N) (hab : a ≠ b)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {a,b}) :
    A = A a • braidRoot a b := by
  funext i
  by_cases hia : i = a
  · subst i; simp [braidRoot,unitVec,hab]
  by_cases hib : i = b
  · subst i
    simpa [braidRoot,unitVec,Ne.symm hab] using row_other_endpoint A a b hab hsum hsupp
  · simp [braidRoot,unitVec,hia,hib,row_zero_off_pair A a b hsupp i hia hib]

theorem sign_difference_mul (x : ℝ) :
    ((if 0 < x then (1:ℝ) else 0) - (if 0 < -x then 1 else 0)) * x = |x| := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [if_neg (not_lt.mpr (le_of_lt hx)),if_pos (neg_pos.mpr hx),abs_of_neg hx]
    ring
  · simp [hx]
  · rw [if_pos hx,if_neg (not_lt.mpr (le_of_lt (neg_neg_of_pos hx))),abs_of_pos hx]
    ring

/-- No orientation or nonzero assumption on the actual row is imposed. -/
theorem edgeCoinDifference_smul (A : Point N) (a b : Fin N) (hab : a ≠ b)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {a,b}) :
    edgeCoinDifference A a b • A = |A a| • braidRoot a b := by
  calc
    _ = edgeCoinDifference A a b • (A a • braidRoot a b) := by
      rw [← row_eq_root_smul A a b hab hsum hsupp]
    _ = |A a| • braidRoot a b := by
      rw [smul_smul,edgeCoinDifference,row_other_endpoint A a b hab hsum hsupp,
        sign_difference_mul]

/-- A nonempty zero-sum row supported on a pair uses both endpoints. -/
theorem rowSupport_eq_pair_of_nonempty (A : Point N) (a b : Fin N) (hab : a ≠ b)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {a,b})
    (hne : (rowSupport A).Nonempty) : rowSupport A = {a,b} := by
  have haa : A a ≠ 0 := by
    intro ha
    obtain ⟨i,hi⟩ := hne
    have hrow := row_eq_root_smul A a b hab hsum hsupp
    rw [ha,zero_smul] at hrow
    exact ((mem_rowSupport A i).mp hi) (congrFun hrow i)
  have hbb : A b ≠ 0 := by rw [row_other_endpoint A a b hab hsum hsupp]; exact neg_ne_zero.mpr haa
  apply Finset.Subset.antisymm hsupp
  intro i hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · subst i; exact (mem_rowSupport A a).mpr haa
  · have : i = b := Finset.mem_singleton.mp hi
    subst i; exact (mem_rowSupport A b).mpr hbb

/-- Every original parallel row index occurs, with unrestricted real weight. -/
noncomputable def braidEdgeRows (A : Fin h₁ → Point N) (a b : Fin N) : Finset (Fin h₁) :=
  Finset.univ.filter fun j => rowSupport (A j) = {a,b}

noncomputable def braidEdgeWeight (A : Fin h₁ → Point N) (W : Fin h₁ → ℝ)
    (a b : Fin N) : ℝ := - ∑ j in braidEdgeRows A a b, W j * |A j a|

noncomputable def braidCoinColumn (A : Fin h₁ → Point N) (W : Fin h₁ → ℝ)
    (a b : Fin N) : Point N :=
  ∑ j in braidEdgeRows A a b, W j • (edgeCoinDifference (A j) a b • A j)

theorem braidCoinColumn_eq (A : Fin h₁ → Point N) (W : Fin h₁ → ℝ)
    (a b : Fin N) (hab : a ≠ b) (hsum : ∀ j, ∑ i, A j i = 0) :
    braidCoinColumn A W a b = - braidEdgeWeight A W a b • braidRoot a b := by
  classical
  unfold braidCoinColumn braidEdgeWeight
  rw [neg_neg,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  have hsupp : rowSupport (A j) ⊆ {a,b} := by
    exact (Finset.mem_filter.mp hj).2.le
  rw [edgeCoinDifference_smul (A j) a b hab (hsum j) hsupp,smul_smul]

/-- Exact-support and nonempty contained-support selections are identical. -/
theorem braidEdgeRows_eq_nonempty_subset (A : Fin h₁ → Point N)
    (a b : Fin N) (hab : a ≠ b) (hsum : ∀ j, ∑ i, A j i = 0) :
    braidEdgeRows A a b = Finset.univ.filter (fun j =>
      (rowSupport (A j)).Nonempty ∧ rowSupport (A j) ⊆ {a,b}) := by
  classical
  ext j
  simp only [braidEdgeRows,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h; rw [h]; exact ⟨⟨a,by simp⟩,Finset.Subset.refl _⟩
  · rintro ⟨hne,hsub⟩
    exact rowSupport_eq_pair_of_nonempty (A j) a b hab (hsum j) hsub hne

/-- The empty-support alternative is precisely the zero row. -/
theorem row_eq_zero_of_support_empty (A : Point N) (h : rowSupport A = ∅) : A = 0 := by
  funext i
  by_contra hi
  have hm := (mem_rowSupport A i).mpr hi
  rw [h] at hm
  exact Finset.not_mem_empty i hm

/-- Containment alone permits only zero rows and full two-endpoint rows. -/
theorem rowSupport_empty_or_pair (A : Point N) (a b : Fin N) (hab : a ≠ b)
    (hsum : ∑ i, A i = 0) (hsupp : rowSupport A ⊆ {a,b}) :
    rowSupport A = ∅ ∨ rowSupport A = {a,b} := by
  classical
  by_cases hne : (rowSupport A).Nonempty
  · exact Or.inr (rowSupport_eq_pair_of_nonempty A a b hab hsum hsupp hne)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

/-- Adding every zero row to the edge filter leaves its real coefficient unchanged. -/
theorem sum_supported_abs_eq (A : Fin h₁ → Point N) (W : Fin h₁ → ℝ)
    (a b : Fin N) (hab : a ≠ b) (hsum : ∀ j, ∑ i, A j i = 0) :
    (∑ j in Finset.univ.filter (fun j => rowSupport (A j) ⊆ {a,b}), W j * |A j a|) =
      ∑ j in braidEdgeRows A a b, W j * |A j a| := by
  classical
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.le⟩
  · intro j hj hjnot
    have hsupp := (Finset.mem_filter.mp hj).2
    rcases rowSupport_empty_or_pair (A j) a b hab (hsum j) hsupp with hempty | hpair
    · rw [row_eq_zero_of_support_empty (A j) hempty]
      simp
    · exact False.elim (hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpair⟩))

/-- Arbitrary finite indexed aggregation under containment hypotheses, including zeros. -/
theorem sum_edgeCoinDifference_smul (A : Fin h₁ → Point N) (W : Fin h₁ → ℝ)
    (s : Finset (Fin h₁)) (a b : Fin N) (hab : a ≠ b)
    (hsum : ∀ j ∈ s, ∑ i, A j i = 0)
    (hsupp : ∀ j ∈ s, rowSupport (A j) ⊆ {a,b}) :
    (∑ j in s, W j • (edgeCoinDifference (A j) a b • A j)) =
      (∑ j in s, W j * |A j a|) • braidRoot a b := by
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [edgeCoinDifference_smul (A j) a b hab (hsum j hj) (hsupp j hj),smul_smul]

/-- Network specialization uses actual first-layer coordinates and real weights. -/
theorem normalizedNetwork_braidCoinColumn (net : NormalizedNetwork N h₁ h₂)
    (hnorm : net.TranslationNormalized) (k : Fin h₂) (a b : Fin N) (hab : a ≠ b) :
    braidCoinColumn net.A (net.W k) a b =
      - braidEdgeWeight net.A (net.W k) a b • braidRoot a b :=
  braidCoinColumn_eq net.A (net.W k) a b hab hnorm.1

end MaxCaterpillar.Frontier.RandomRestriction
