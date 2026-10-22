import MaxCaterpillar.CPWL
import MaxCaterpillar.RationalWidth

/-! # Rational outer layers for signed sums of maxima (Version 2)

Version 1 (`Sharing.lean`, `CPWL.lean`) only asserts that the networks for
`∑ₜ εₜ max_N(…)` exist. For arbitrary affine pieces the first-layer weights
are the piece slopes, which can be irrational, and the constant terms of the
pieces need first-layer biases. The honest Version 2 refinement is:

* the second hidden layer and the output layer have rational weights and zero
  biases (`Network.HasRationalOuterLayers`), provided the signs `εₜ` are
  rational;
* every neuron of the first hidden layer computes `g_a - g_b`, `g_a`, or
  `-g_a` for affine pieces `g_a(x) = ∑ₗ Gw a l xₗ + Gb a` (`IsPieceRow`);
  hence rational pieces give rational weights and biases, and linear pieces
  (`Gb = 0`) give zero biases.

The key input is `exists_rat_caterpillarExpansion`: the Caterpillar Net
expansion of `max_{r+2}` used in `Sharing.lean` has rational coefficients.
-/

open BigOperators

namespace MaxCaterpillar

/-! ## Predicates -/

/-- Version 2 refinement: the second hidden layer and the output layer have
rational weights and zero biases. Nothing is asserted about the first hidden
layer. -/
def Network.HasRationalOuterLayers {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) : Prop :=
  (∀ k j, ∃ q : ℚ, (q : ℝ) = net.W₂ k j) ∧ (∀ k, ∃ q : ℚ, (q : ℝ) = net.w₃ k) ∧
    net.b₂ = 0 ∧ net.b₃ = 0

/-- Version 2 refinement: all three bias arrays are rational. -/
def Network.HasRationalBiases {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) : Prop :=
  (∀ j, ∃ q : ℚ, (q : ℝ) = net.b₁ j) ∧ (∀ k, ∃ q : ℚ, (q : ℝ) = net.b₂ k) ∧
    ∃ q : ℚ, (q : ℝ) = net.b₃

/-- The weight row `w` and bias `β` of a first-layer neuron are those of
`g_a - g_b`, of `g_a`, or of `-g_a`, where `g_a(x) = ∑ₗ Gw a l xₗ + Gb a`. -/
def IsPieceRow {d p : ℕ} (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ) (w : Fin d → ℝ)
    (β : ℝ) : Prop :=
  (∃ a b, w = Gw a - Gw b ∧ β = Gb a - Gb b) ∨ (∃ a, w = Gw a ∧ β = Gb a) ∨
    ∃ a, w = -Gw a ∧ β = -Gb a

section PieceRow

variable {d p : ℕ} {Gw : Fin p → Fin d → ℝ} {Gb : Fin p → ℝ} {w : Fin d → ℝ} {β : ℝ}

theorem IsPieceRow.weight_mem (h : IsPieceRow Gw Gb w β)
    (hGw : ∀ a l, Gw a l ∈ ratField) (l : Fin d) : w l ∈ ratField := by
  rcases h with ⟨a, b, rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨a, rfl, -⟩
  · exact Subfield.sub_mem _ (hGw a l) (hGw b l)
  · exact hGw a l
  · exact Subfield.neg_mem _ (hGw a l)

theorem IsPieceRow.bias_mem (h : IsPieceRow Gw Gb w β)
    (hGb : ∀ a, Gb a ∈ ratField) : β ∈ ratField := by
  rcases h with ⟨a, b, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩
  · exact Subfield.sub_mem _ (hGb a) (hGb b)
  · exact hGb a
  · exact Subfield.neg_mem _ (hGb a)

theorem IsPieceRow.bias_eq_zero (h : IsPieceRow Gw Gb w β) (hGb : Gb = 0) : β = 0 := by
  subst hGb
  rcases h with ⟨a, b, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ <;> simp

end PieceRow

/-- Rational outer layers plus a rational first layer give rational weights
and rational biases. -/
theorem Network.rational_of_outer {N h₁ h₂ : ℕ} {net : Network N h₁ h₂}
    (ho : net.HasRationalOuterLayers) (hW : ∀ j i, net.W₁ j i ∈ ratField)
    (hb : ∀ j, net.b₁ j ∈ ratField) : net.HasRationalWeights ∧ net.HasRationalBiases := by
  obtain ⟨hW₂, hw₃, hb₂, hb₃⟩ := ho
  refine ⟨⟨fun j i => mem_ratField_iff.mp (hW j i), hW₂, hw₃⟩,
    fun j => mem_ratField_iff.mp (hb j), fun k => ⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · rw [hb₂, Rat.cast_zero]; rfl
  · rw [hb₃, Rat.cast_zero]

theorem Network.zeroBiases_of_outer {N h₁ h₂ : ℕ} {net : Network N h₁ h₂}
    (ho : net.HasRationalOuterLayers) (hb : ∀ j, net.b₁ j = 0) : net.HasZeroBiases :=
  ⟨funext hb, ho.2.2.1, ho.2.2.2⟩

/-! ## Assembling a network, with its parameters recorded -/

theorem exists_network_of_families_spec {d : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (W₁ : ι₁ → Fin d → ℝ) (b₁ : ι₁ → ℝ) (W₂ : ι₂ → ι₁ → ℝ) (b₂ : ι₂ → ℝ)
    (w₃ : ι₂ → ℝ) (b₃ : ℝ) :
    ∃ net : Network d (Fintype.card ι₁) (Fintype.card ι₂), (∀ x, net.eval x =
      (∑ k, w₃ k * relu ((∑ j, W₂ k j * relu ((∑ i, W₁ j i * x i) + b₁ j)) + b₂ k))
        + b₃) ∧
      (∀ j, ∃ j', net.W₁ j = W₁ j' ∧ net.b₁ j = b₁ j') ∧
      (∀ k j, ∃ k' j', net.W₂ k j = W₂ k' j') ∧
      (∀ k, ∃ k', net.b₂ k = b₂ k' ∧ net.w₃ k = w₃ k') ∧ net.b₃ = b₃ := by
  classical
  let e₁ := Fintype.equivFin ι₁
  let e₂ := Fintype.equivFin ι₂
  refine ⟨⟨fun j => W₁ (e₁.symm j), fun j => b₁ (e₁.symm j),
    fun k j => W₂ (e₂.symm k) (e₁.symm j), fun k => b₂ (e₂.symm k),
    fun k => w₃ (e₂.symm k), b₃⟩, fun x => ?_, fun j => ⟨_, rfl, rfl⟩,
    fun k j => ⟨_, _, rfl⟩, fun k => ⟨_, rfl, rfl⟩, rfl⟩
  have h : ∀ k', (∑ j, W₂ k' (e₁.symm j) *
      relu ((∑ i, W₁ (e₁.symm j) i * x i) + b₁ (e₁.symm j))) =
      ∑ j, W₂ k' j * relu ((∑ i, W₁ j i * x i) + b₁ j) := fun k' =>
    e₁.symm.sum_comp (fun j => W₂ k' j * relu ((∑ i, W₁ j i * x i) + b₁ j))
  simp only [Network.eval, h]
  rw [e₂.symm.sum_comp (fun k => w₃ k *
    relu ((∑ j, W₂ k j * relu ((∑ i, W₁ j i * x i) + b₁ j)) + b₂ k))]

/-- Enlarging the second hidden layer by zero neurons keeps the first layer and
rational outer layers. -/
theorem Network.exists_widen_outer {N h₁ h₂ h₂' : ℕ} (net : Network N h₁ h₂)
    (hle : h₂ ≤ h₂') :
    ∃ net' : Network N h₁ h₂', (∀ x, net'.eval x = net.eval x) ∧ net'.W₁ = net.W₁ ∧
      net'.b₁ = net.b₁ ∧ (net.HasRationalOuterLayers → net'.HasRationalOuterLayers) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨net.padSecond m, net.padSecond_eval m, rfl, rfl, ?_⟩
  rintro ⟨h2, h3, hb₂, hb₃⟩
  refine ⟨fun k j => ?_, fun k => ?_, ?_, hb₃⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Network.padSecond, Fin.append_left]; exact h2 k j
    · simp only [Network.padSecond, Fin.append_right]; exact ⟨0, Rat.cast_zero⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Network.padSecond, Fin.append_left]; exact h3 k
    · simp only [Network.padSecond, Fin.append_right]; exact ⟨0, Rat.cast_zero⟩
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Network.padSecond, Fin.append_left]; exact congrFun hb₂ k
    · simp only [Network.padSecond, Fin.append_right]; rfl

/-! ## Rational pair-hinge expansions -/

/-- All coefficients `V`, `c`, `q` of a pair-hinge expansion are rational. -/
def PairExpansion.IsRational {N : ℕ} [NeZero N] {ι φ : Type*} [Fintype ι] [Fintype φ]
    (E : PairExpansion N ι φ) : Prop :=
  (∀ k j, E.V k j ∈ ratField) ∧ (∀ k, E.c k ∈ ratField) ∧ ∀ j, E.q j ∈ ratField

/-- **Merged remainder, rational version.** As `exists_network_sum_maximum`,
for a rational expansion, rational coefficients `e`, and rational readouts of
the coordinates and pair hinges. The first hidden layer is the given one, and
the outer layers are rational with zero biases. Version 2; Version 1 is
`exists_network_sum_maximum`. -/
theorem exists_network_sum_maximum_rational {d N : ℕ} [NeZero N]
    {ι φ ι₁ τ : Type*} [Fintype ι] [Fintype φ] [Fintype ι₁] [Fintype τ]
    (E : PairExpansion N ι φ) (hE : E.IsRational)
    (W₁ : ι₁ → Fin d → ℝ) (b₁ : ι₁ → ℝ) (y : τ → Point d → Point N) (e : τ → ℝ)
    (he : ∀ s, e s ∈ ratField)
    (hcoord : ∀ s i, ∃ κ : ι₁ → ℝ, (∀ l, κ l ∈ ratField) ∧ ∀ x,
      ∑ l, κ l * relu ((∑ i', W₁ l i' * x i') + b₁ l) = y s x i)
    (hhinge : ∀ s i j, ∃ κ : ι₁ → ℝ, (∀ l, κ l ∈ ratField) ∧ ∀ x,
      ∑ l, κ l * relu ((∑ i', W₁ l i' * x i') + b₁ l) = relu (y s x i - y s x j)) :
    ∃ net : Network d (Fintype.card ι₁) (Fintype.card τ * Fintype.card ι + 2),
      (∀ x, net.eval x = ∑ s, e s * Maximum N (y s x)) ∧ net.HasRationalOuterLayers ∧
      ∀ j, ∃ j', net.W₁ j = W₁ j' ∧ net.b₁ j = b₁ j' := by
  classical
  choose κC hκCr hκC using hcoord
  choose κH hκHr hκH using hhinge
  obtain ⟨row, hrow_def⟩ : ∃ row : τ × ι → ι₁ → ℝ,
      row = fun p => ∑ j, E.V p.2 j • κH p.1 (E.u j) (E.v j) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ι₁ → ℝ,
      ρ = ∑ s, e s • (κC s E.i₀ + ∑ j, E.q j • κH s (E.u j) (E.v j)) := ⟨_, rfl⟩
  have hrow_mem : ∀ p l, row p l ∈ ratField := fun p l => by
    rw [hrow_def]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_mem_ratField _ fun j _ => Subfield.mul_mem _ (hE.1 _ _) (hκHr _ _ _ _)
  have hρ_mem : ∀ l, ρ l ∈ ratField := fun l => by
    rw [hρ_def]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact sum_mem_ratField _ fun s _ => Subfield.mul_mem _ (he s)
      (Subfield.add_mem _ (hκCr _ _ _) (sum_mem_ratField _ fun j _ =>
        Subfield.mul_mem _ (hE.2.2 _) (hκHr _ _ _ _)))
  let W₂ : (τ × ι) ⊕ Fin 2 → ι₁ → ℝ :=
    Sum.elim row (fun m => if m = 0 then ρ else -ρ)
  let w₃ : (τ × ι) ⊕ Fin 2 → ℝ :=
    Sum.elim (fun p => e p.1 * E.c p.2) (fun m => if m = 0 then 1 else -1)
  have hcard : Fintype.card ((τ × ι) ⊕ Fin 2) =
      Fintype.card τ * Fintype.card ι + 2 := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [← hcard]
  obtain ⟨net, hnet, hW₁, hW₂, hb₂w₃, hb₃⟩ :=
    exists_network_of_families_spec W₁ b₁ W₂ (fun _ => 0) w₃ 0
  refine ⟨net, fun x => ?_, ⟨fun k j => ?_, fun k => ?_, ?_, hb₃⟩, hW₁⟩
  · rw [hnet x, add_zero]
    -- Readouts of the rows.
    have hrow : ∀ p : τ × ι, readout W₁ b₁ (row p) x =
        ∑ j, E.V p.2 j * relu (y p.1 x (E.u j) - y p.1 x (E.v j)) := by
      intro p
      simp only [hrow_def, readout_sum, readout_smul]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show readout W₁ b₁ (κH p.1 (E.u j) (E.v j)) x = _ from hκH _ _ _ x]
    have hρ : readout W₁ b₁ ρ x = ∑ s, e s * (y s x E.i₀ +
        ∑ j, E.q j * relu (y s x (E.u j) - y s x (E.v j))) := by
      simp only [hρ_def, readout_sum, readout_smul, readout_add]
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 2
      · exact hκC s E.i₀ x
      · exact Finset.sum_congr rfl fun j _ => by
          rw [show readout W₁ b₁ (κH s (E.u j) (E.v j)) x = _ from hκH _ _ _ x]
    have hgoal : ∀ k, (∑ j, W₂ k j * relu ((∑ i, W₁ j i * x i) + b₁ j)) + 0 =
        readout W₁ b₁ (W₂ k) x := fun k => add_zero _
    simp only [hgoal]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Sum.elim_inl, Sum.elim_inr, W₂, w₃, if_pos rfl, ite_true,
      if_neg (show (1 : Fin 2) ≠ 0 by decide), readout_neg, hrow, hρ, one_mul,
      neg_one_mul]
    rw [← sub_eq_add_neg, relu_sub_relu_neg', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [E.spec (y s x)]
    simp only [mul_add, Finset.mul_sum, ← mul_assoc]
    ring
  · obtain ⟨k', j', h⟩ := hW₂ k j
    rw [h]
    refine mem_ratField_iff.mp ?_
    rcases k' with p | m
    · exact hrow_mem p j'
    · show (if m = 0 then ρ else -ρ) j' ∈ ratField
      split_ifs
      · exact hρ_mem j'
      · exact Subfield.neg_mem _ (hρ_mem j')
  · obtain ⟨k', -, h⟩ := hb₂w₃ k
    rw [h]
    refine mem_ratField_iff.mp ?_
    rcases k' with p | m
    · exact Subfield.mul_mem _ (he p.1) (hE.2.1 p.2)
    · show (if m = 0 then (1 : ℝ) else -1) ∈ ratField
      split_ifs
      · exact Subfield.one_mem _
      · exact Subfield.neg_mem _ (Subfield.one_mem _)
  · funext k
    obtain ⟨k', h, -⟩ := hb₂w₃ k
    exact h

/-! ## The first hidden layer `Φ ∘ g` consists of piece rows -/

section Pieces

open MaxNN.Caterpillar.Corrections MaxNN.Width

theorem compactFeatureLayer_row (n : ℕ) (j : Fin (compactWidth n)) :
    ((∃ a b : Fin (n + 1), (compactFeatureLayer n).A j =
        fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) ∨
      (∃ a : Fin (n + 1), (compactFeatureLayer n).A j = fun c => if c = a then 1 else 0) ∨
      ∃ a : Fin (n + 1), (compactFeatureLayer n).A j = fun c => -(if c = a then 1 else 0)) ∧
    (compactFeatureLayer n).b j = 0 := by
  unfold compactFeatureLayer
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [stack_A_castAdd, stack_b_castAdd]
    refine ⟨?_, rfl⟩
    by_cases hj : j = 0
    · exact Or.inr (Or.inl ⟨0, funext fun c => by simp only [rootSignRows, if_pos hj]⟩)
    · exact Or.inr (Or.inr ⟨0, funext fun c => by simp only [rootSignRows, if_neg hj]⟩)
  · rw [stack_A_natAdd, stack_b_natAdd]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [stack_A_castAdd, stack_b_castAdd]
      exact ⟨Or.inl ⟨j.succ, 0, rfl⟩, rfl⟩
    · rw [stack_A_natAdd, stack_b_natAdd]
      exact ⟨Or.inl ⟨prFst j, prSnd j, rfl⟩, rfl⟩

private theorem sum_delta_mul {m : ℕ} (a : Fin m) (x : Fin m → ℝ) :
    ∑ c, (if c = a then (1 : ℝ) else 0) * x c = x a :=
  MaxNN.Affine.delta_row_sum a x

/-- Every neuron of the first hidden layer `Φ ∘ g` computes `g_a - g_b`,
`g_a`, or `-g_a`. -/
theorem isPieceRow_pieces {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (j : Fin (compactWidth n)) : IsPieceRow Gw Gb (piecesW₁ Gw j) (piecesb₁ Gb j) := by
  obtain ⟨hA, hb⟩ := compactFeatureLayer_row n j
  unfold piecesW₁ piecesb₁
  rw [hb, add_zero]
  rcases hA with ⟨a, b, hA⟩ | ⟨a, hA⟩ | ⟨a, hA⟩ <;> simp only [hA]
  · refine Or.inl ⟨a, b, funext fun i => ?_, ?_⟩
    · simp only [sub_mul, Finset.sum_sub_distrib, sum_delta_mul, Pi.sub_apply]
    · simp only [sub_mul, Finset.sum_sub_distrib, sum_delta_mul]
  · exact Or.inr (Or.inl ⟨a, funext fun i => sum_delta_mul a _, sum_delta_mul a _⟩)
  · refine Or.inr (Or.inr ⟨a, funext fun i => ?_, ?_⟩)
    · simp only [neg_mul, Finset.sum_neg_distrib, sum_delta_mul, Pi.neg_apply]
    · simp only [neg_mul, Finset.sum_neg_distrib, sum_delta_mul]

theorem pieces_coord_span_rational {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ)
    (Gb : Fin (n + 1) → ℝ) (a : Fin (n + 1)) :
    ∃ κ : Fin (compactWidth n) → ℝ, (∀ l, κ l ∈ ratField) ∧ ∀ x,
      ∑ j, κ j * relu ((∑ i, piecesW₁ Gw j i * x i) + piecesb₁ Gb j) = pieces Gw Gb x a :=
  ⟨compactCoordCoeff a, ratVec_compactCoordCoeff a, fun x => by
    rw [piecesW₁_readout, sum_compactCoordCoeff, compactCoordLin_feat]⟩

theorem pieces_hinge_span_rational {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ)
    (Gb : Fin (n + 1) → ℝ) (a b : Fin (n + 1)) :
    ∃ κ : Fin (compactWidth n) → ℝ, (∀ l, κ l ∈ ratField) ∧ ∀ x,
      ∑ j, κ j * relu ((∑ i, piecesW₁ Gw j i * x i) + piecesb₁ Gb j) =
        relu (pieces Gw Gb x a - pieces Gw Gb x b) :=
  ⟨compactHingeCoeff a b, ratVec_compactHingeCoeff a b, fun x => by
    rw [piecesW₁_readout, sum_compactHingeCoeff, compactHingeLin_feat]
    rfl⟩

end Pieces

/-! ## Shared affine pieces -/

open MaxNN.Caterpillar.Corrections in
/-- **Shared pieces, rational version.** As `exists_network_shared_pieces`, for
a rational expansion and rational coefficients `ε`: the outer layers are
rational with zero biases, and every first-layer neuron computes `g_a - g_b`,
`g_a`, or `-g_a`. Version 2; Version 1 is `exists_network_shared_pieces`. -/
theorem exists_network_shared_pieces_rational {d N n T : ℕ} [NeZero N]
    {ι φ : Type*} [Fintype ι] [Fintype φ] (E : PairExpansion N ι φ) (hE : E.IsRational)
    (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (α : Fin T → Fin N → Fin (n + 1)) (ε : Fin T → ℝ) (hε : ∀ t, ε t ∈ ratField) :
    ∃ net : Network d ((n + 1).choose 2 + (n + 1) + 1)
      ((imageSets α).card * Fintype.card ι + 2),
      (∀ x, net.eval x = ∑ t, ε t * Maximum N (fun i => pieces Gw Gb x (α t i))) ∧
      net.HasRationalOuterLayers ∧ ∀ j, IsPieceRow Gw Gb (net.W₁ j) (net.b₁ j) := by
  classical
  have hrep : ∀ S : imageSets α, ∃ t, Finset.univ.image (α t) = S.1 := fun S => by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp S.2
    exact ⟨t, ht⟩
  choose rep hrep using hrep
  let e : imageSets α → ℝ := fun S =>
    ∑ t in Finset.univ.filter (fun t => Finset.univ.image (α t) = S.1), ε t
  have he : ∀ S, e S ∈ ratField := fun S => sum_mem_ratField _ fun t _ => hε t
  rw [show (n + 1).choose 2 + (n + 1) + 1 = Fintype.card (Fin (compactWidth n)) by
      rw [Fintype.card_fin, compactWidth_eq],
    show (imageSets α).card = Fintype.card (imageSets α) from (Fintype.card_coe _).symm]
  obtain ⟨net, hnet, hout, hrow⟩ := exists_network_sum_maximum_rational E hE (piecesW₁ Gw)
    (piecesb₁ Gb) (fun S x i => pieces Gw Gb x (α (rep S) i)) e he
    (fun S _ => pieces_coord_span_rational Gw Gb _)
    (fun S _ _ => pieces_hinge_span_rational Gw Gb _ _)
  refine ⟨net, fun x => ?_, hout, fun j => ?_⟩
  · rw [hnet x, ← Finset.sum_fiberwise_of_maps_to (t := imageSets α)
      (g := fun t => Finset.univ.image (α t))
      (fun t _ => Finset.mem_image_of_mem _ (Finset.mem_univ t)),
      ← Finset.sum_coe_sort (imageSets α)]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [maximum_comp_eq (pieces Gw Gb x) (α t) (α (rep S))
      ((Finset.mem_filter.mp ht).2.trans (hrep S).symm)]
  · obtain ⟨j', hW, hb⟩ := hrow j
    rw [hW, hb]
    exact isPieceRow_pieces Gw Gb j'

/-! ## Arbitrary affine maps: one feature block per term -/

open MaxNN.Caterpillar.Corrections in
/-- **Merged remainder, no shared pieces, rational version.** As
`exists_network_sum_affine_maximum`: the outer layers are rational with zero
biases, and every first-layer neuron computes `g - g'`, `g`, or `-g` for two
affine components `g, g'` of one map `Aₜ`. Version 2; Version 1 is
`exists_network_sum_affine_maximum`. -/
theorem exists_network_sum_affine_maximum_rational {d n T : ℕ}
    {ι φ : Type*} [Fintype ι] [Fintype φ] (E : PairExpansion (n + 1) ι φ)
    (hE : E.IsRational)
    (Aw : Fin T → Fin (n + 1) → Fin d → ℝ) (Ab : Fin T → Fin (n + 1) → ℝ)
    (ε : Fin T → ℝ) (hε : ∀ t, ε t ∈ ratField) :
    ∃ net : Network d (T * ((n + 1).choose 2 + (n + 1) + 1)) (T * Fintype.card ι + 2),
      (∀ x, net.eval x = ∑ t, ε t * Maximum (n + 1) (pieces (Aw t) (Ab t) x)) ∧
      net.HasRationalOuterLayers ∧ ∀ j, ∃ t, IsPieceRow (Aw t) (Ab t) (net.W₁ j) (net.b₁ j) := by
  classical
  rw [show T * ((n + 1).choose 2 + (n + 1) + 1) =
      Fintype.card (Fin T × Fin (compactWidth n)) by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, compactWidth_eq]]
  have hblock : ∀ (t : Fin T) (κ₀ : Fin (compactWidth n) → ℝ), (∀ l, κ₀ l ∈ ratField) →
      ∀ l : Fin T × Fin (compactWidth n), (if l.1 = t then κ₀ l.2 else 0) ∈ ratField :=
    fun t κ₀ hκ₀ l => by
      split_ifs
      · exact hκ₀ _
      · exact Subfield.zero_mem _
  have h := exists_network_sum_maximum_rational E hE
    (fun p : Fin T × Fin (compactWidth n) => piecesW₁ (Aw p.1) p.2)
    (fun p => piecesb₁ (Ab p.1) p.2) (fun t x => pieces (Aw t) (Ab t) x) ε hε
    (fun t i => by
      obtain ⟨κ₀, hκ₀r, hκ₀⟩ := pieces_coord_span_rational (Aw t) (Ab t) i
      exact ⟨fun p => if p.1 = t then κ₀ p.2 else 0, hblock t κ₀ hκ₀r, fun x => by
        rw [sum_block (fun p : Fin T × Fin (compactWidth n) =>
          relu ((∑ i', piecesW₁ (Aw p.1) p.2 i' * x i') + piecesb₁ (Ab p.1) p.2))]
        exact hκ₀ x⟩)
    (fun t i j => by
      obtain ⟨κ₀, hκ₀r, hκ₀⟩ := pieces_hinge_span_rational (Aw t) (Ab t) i j
      exact ⟨fun p => if p.1 = t then κ₀ p.2 else 0, hblock t κ₀ hκ₀r, fun x => by
        rw [sum_block (fun p : Fin T × Fin (compactWidth n) =>
          relu ((∑ i', piecesW₁ (Aw p.1) p.2 i' * x i') + piecesb₁ (Ab p.1) p.2))]
        exact hκ₀ x⟩)
  rw [Fintype.card_fin] at h
  obtain ⟨net, hnet, hout, hrow⟩ := h
  refine ⟨net, hnet, hout, fun j => ?_⟩
  obtain ⟨⟨t, j'⟩, hW, hb⟩ := hrow j
  exact ⟨t, by rw [hW, hb]; exact isPieceRow_pieces (Aw t) (Ab t) j'⟩

/-! ## The Caterpillar Net expansion is rational -/

section Caterpillar

open MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.Width

/-- The Caterpillar Net expansion of `max_{r+2}` of `exists_caterpillarExpansion`
has rational coefficients: its heads are integer vectors and its key and
remainder coefficients are rational (`canonicalNormalizedCoeff_mem_ratField`).
Version 2; Version 1 is `exists_caterpillarExpansion`. -/
theorem exists_rat_caterpillarExpansion (r : ℕ) (hr : 1 ≤ r) :
    ∃ E : PairExpansion (r + 1 + 1) (caterpillarKeys r) (Fin (compactWidth (r + 1))),
      E.IsRational := by
  classical
  set K := caterpillarKeys r
  let c := Canonical.canonicalNormalizedCoeff r
  let a := absorbedRemainderCoeff (Canonical.canonicalActiveKeys r)
    (Canonical.canonicalNormalizedCoeff r) (Canonical.canonicalRemainderCoeff r)
  let q := compactOfPairCoeff a
  have hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v :=
    essentialKeys_labels _ fun k hk => normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  have hmax : ∀ x, MaxNN.MAX (r + 1 + 1) x =
      ∑ k in K, c k * realUnitY k x + ∑ j, q j * compactFeat (r + 1) x j := fun x =>
    (compactEssentialNetwork_computes r hr x).symm.trans
      (compactDictionaryNetwork_eval K c q hK x)
  have ha : RatVec a := (ratVec_canonicalRemainderCoeff hr).add (ratVec_sum _ fun k _ =>
    RatVec.smul (canonicalNormalizedCoeff_mem_ratField hr k) (ratVec_rootHingeCoeff _))
  refine ⟨⟨0, fun j => (featurePair (r + 1) j).1, fun j => (featurePair (r + 1) j).2,
    fun k j => compactRealUnitCoeff k.1 j, fun k => c k.1, q, fun y => ?_⟩,
    fun k j => ratVec_compactRealUnitCoeff
      (ratVec_normalizedKey (Finset.mem_filter.mp (essentialKeys_subset _ k.2)).1) j,
    fun k => canonicalNormalizedCoeff_mem_ratField hr k.1, ratVec_compactOfPairCoeff ha⟩
  have hz := hmax (fun i => y i - y 0)
  have hshift := MaxNN.MAX_add_const (fun i => y i - y 0) (y 0)
  simp only [sub_add_cancel] at hshift
  rw [Internal.maximum_eq_MAX, hshift, hz]
  simp only [compactFeat_sub_root, realUnitY_eq_relu]
  rw [← Finset.sum_coe_sort K]
  have hunit : ∀ k : K, realUnitArg k.1 (fun i => y i - y 0) =
      ∑ j, compactRealUnitCoeff k.1 j *
        relu (y (featurePair (r + 1) j).1 - y (featurePair (r + 1) j).2) := fun k => by
    rw [← sum_compactRealUnitCoeff k.1 (hK k.1 k.2)]
    simp only [compactFeat_sub_root]
  simp only [hunit, relu_eq_maxnn]
  ring

/-- **Caterpillar Net, shared affine pieces, rational outer layers.** The
network of `caterpillar_shared_pieces` can be chosen so that, for rational
`εₜ`, its second hidden layer and output layer have rational weights and zero
biases, and every neuron of its first hidden layer computes `g_a - g_b`, `g_a`,
or `-g_a`. Version 2; Version 1 is `caterpillar_shared_pieces`. -/
theorem caterpillar_shared_pieces_rational {d n T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin (n + 1)) (ε : Fin T → ℝ)
    (hε : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t) :
    ∃ net : Network d ((n + 1).choose 2 + (n + 1) + 1)
      ((imageSets α).card * (secondWidth (r + 1 + 1) - 2) + 2),
      (∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (fun i => pieces Gw Gb x (α t i))) ∧
      net.HasRationalOuterLayers ∧ ∀ j, IsPieceRow Gw Gb (net.W₁ j) (net.b₁ j) := by
  obtain ⟨E, hE⟩ := exists_rat_caterpillarExpansion r hr
  have hK := card_caterpillarKeys_le r hr
  obtain ⟨net, hnet, hout, hrow⟩ := exists_network_shared_pieces_rational E hE Gw Gb α ε
    fun t => mem_ratField_iff.mpr (hε t)
  have hle : (imageSets α).card * Fintype.card (caterpillarKeys r) + 2 ≤
      (imageSets α).card * (secondWidth (r + 1 + 1) - 2) + 2 := by
    rw [Fintype.card_coe]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2
  obtain ⟨net', heval, hW, hb, hout'⟩ := net.exists_widen_outer hle
  exact ⟨net', fun x => (heval x).trans (hnet x), hout' hout,
    fun j => by rw [hW, hb]; exact hrow j⟩

/-- `caterpillar_shared_pieces_rational` with exactly `r + 2` distinct pieces
in every term: second width `min(T, C(n+1, r+2)) (h₂ - 2) + 2`. Version 2;
Version 1 is `caterpillar_shared_pieces_min`. -/
theorem caterpillar_shared_pieces_min_rational {d n T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin (n + 1)) (hα : ∀ t, Function.Injective (α t))
    (ε : Fin T → ℝ) (hε : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t) :
    ∃ net : Network d ((n + 1).choose 2 + (n + 1) + 1)
      (min T ((n + 1).choose (r + 1 + 1)) * (secondWidth (r + 1 + 1) - 2) + 2),
      (∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (fun i => pieces Gw Gb x (α t i))) ∧
      net.HasRationalOuterLayers ∧ ∀ j, IsPieceRow Gw Gb (net.W₁ j) (net.b₁ j) := by
  obtain ⟨net, hnet, hout, hrow⟩ := caterpillar_shared_pieces_rational r hr Gw Gb α ε hε
  obtain ⟨net', heval, hW, hb, hout'⟩ := net.exists_widen_outer
    (Nat.add_le_add_right (Nat.mul_le_mul_right _
      (le_min (card_imageSets_le α) (card_imageSets_le_choose α hα))) 2)
  exact ⟨net', fun x => (heval x).trans (hnet x), hout' hout,
    fun j => by rw [hW, hb]; exact hrow j⟩

/-- **Caterpillar Net, arbitrary affine maps, rational outer layers.** The
network of `caterpillar_sum_affine` can be chosen so that, for rational `εₜ`,
its outer layers are rational with zero biases, and every neuron of its first
hidden layer computes `g - g'`, `g`, or `-g` for components `g, g'` of one
`Aₜ`. Version 2; Version 1 is `caterpillar_sum_affine`. -/
theorem caterpillar_sum_affine_rational {d T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Aw : Fin T → Fin (r + 1 + 1) → Fin d → ℝ) (Ab : Fin T → Fin (r + 1 + 1) → ℝ)
    (ε : Fin T → ℝ) (hε : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t) :
    ∃ net : Network d (T * firstWidth (r + 1 + 1)) (T * (secondWidth (r + 1 + 1) - 2) + 2),
      (∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (pieces (Aw t) (Ab t) x)) ∧
      net.HasRationalOuterLayers ∧
      ∀ j, ∃ t, IsPieceRow (Aw t) (Ab t) (net.W₁ j) (net.b₁ j) := by
  obtain ⟨E, hE⟩ := exists_rat_caterpillarExpansion r hr
  have hK := card_caterpillarKeys_le r hr
  obtain ⟨net, hnet, hout, hrow⟩ := exists_network_sum_affine_maximum_rational E hE Aw Ab ε
    fun t => mem_ratField_iff.mpr (hε t)
  have hle : T * Fintype.card (caterpillarKeys r) + 2 ≤
      T * (secondWidth (r + 1 + 1) - 2) + 2 := by
    rw [Fintype.card_coe]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2
  obtain ⟨net', heval, hW, hb, hout'⟩ := net.exists_widen_outer hle
  exact ⟨net', fun x => (heval x).trans (hnet x), hout' hout,
    fun j => by rw [hW, hb]; exact hrow j⟩

end Caterpillar

/-! ## Any number of pieces -/

/-- `caterpillar_shared_pieces_rational` for any number `p` of pieces. For
`p = 0` there are no terms and the network is zero; its single first-layer
neuron is the zero row. Version 2; Version 1 is `caterpillar_shared_pieces_any`. -/
theorem caterpillar_shared_pieces_any_rational {d p T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin p) (ε : Fin T → ℝ)
    (hε : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t) :
    ∃ net : Network d (p.choose 2 + p + 1)
      ((imageSets α).card * (secondWidth (r + 1 + 1) - 2) + 2),
      (∀ x, net.eval x = ∑ t, ε t *
        Maximum (r + 1 + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i))) ∧
      net.HasRationalOuterLayers ∧
      ∀ j, IsPieceRow Gw Gb (net.W₁ j) (net.b₁ j) ∨ (net.W₁ j = 0 ∧ net.b₁ j = 0) := by
  cases p with
  | zero =>
    have hT : T = 0 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · exact h
      · exact (α ⟨0, h⟩ 0).elim0
    subst hT
    refine ⟨⟨0, 0, 0, 0, 0, 0⟩, fun x => by rw [Network.eval_zero]; rfl,
      ⟨fun k j => ⟨0, Rat.cast_zero⟩, fun k => ⟨0, Rat.cast_zero⟩, rfl, rfl⟩,
      fun j => Or.inr ⟨rfl, rfl⟩⟩
  | succ n =>
    obtain ⟨net, hnet, hout, hrow⟩ := caterpillar_shared_pieces_rational r hr Gw Gb α ε hε
    exact ⟨net, hnet, hout, fun j => Or.inl (hrow j)⟩

/-! ## Rational and linear pieces -/

/-- **Rational pieces.** If the pieces `g_a` and the coefficients `εₜ` are
rational, the network of `caterpillar_shared_pieces_any` can be chosen with
rational weights and rational biases; if moreover every piece is linear
(`Gb = 0`), all its biases vanish. Version 2; Version 1 is
`caterpillar_shared_pieces_any`. -/
theorem caterpillar_shared_pieces_rational_pieces {d p T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin p) (ε : Fin T → ℝ)
    (hGw : ∀ a l, ∃ q : ℚ, (q : ℝ) = Gw a l) (hGb : ∀ a, ∃ q : ℚ, (q : ℝ) = Gb a)
    (hε : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t) :
    ∃ net : Network d (p.choose 2 + p + 1)
      ((imageSets α).card * (secondWidth (r + 1 + 1) - 2) + 2),
      (∀ x, net.eval x = ∑ t, ε t *
        Maximum (r + 1 + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i))) ∧
      net.HasRationalWeights ∧ net.HasRationalBiases ∧ (Gb = 0 → net.HasZeroBiases) := by
  obtain ⟨net, hnet, hout, hrow⟩ := caterpillar_shared_pieces_any_rational r hr Gw Gb α ε hε
  have hGw' : ∀ a l, Gw a l ∈ ratField := fun a l => mem_ratField_iff.mpr (hGw a l)
  have hGb' : ∀ a, Gb a ∈ ratField := fun a => mem_ratField_iff.mpr (hGb a)
  obtain ⟨hw, hb⟩ := Network.rational_of_outer hout
    (fun j i => by
      rcases hrow j with h | ⟨h, -⟩
      · exact h.weight_mem hGw' i
      · rw [h]; exact Subfield.zero_mem _)
    (fun j => by
      rcases hrow j with h | ⟨-, h⟩
      · exact h.bias_mem hGb'
      · rw [h]; exact Subfield.zero_mem _)
  refine ⟨net, hnet, hw, hb, fun h0 => Network.zeroBiases_of_outer hout fun j => ?_⟩
  rcases hrow j with h | ⟨-, h⟩
  · exact h.bias_eq_zero h0
  · exact h

/-- **Rational affine maps.** If all `Aₜ` and `εₜ` are rational, the network of
`caterpillar_sum_affine` can be chosen with rational weights and rational
biases; if moreover every `Aₜ` is linear (`Ab = 0`), all its biases vanish.
Version 2; Version 1 is `caterpillar_sum_affine`. -/
theorem caterpillar_sum_affine_rational_pieces {d T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Aw : Fin T → Fin (r + 1 + 1) → Fin d → ℝ) (Ab : Fin T → Fin (r + 1 + 1) → ℝ)
    (ε : Fin T → ℝ) (hAw : ∀ t i l, ∃ q : ℚ, (q : ℝ) = Aw t i l)
    (hAb : ∀ t i, ∃ q : ℚ, (q : ℝ) = Ab t i) (hε : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t) :
    ∃ net : Network d (T * firstWidth (r + 1 + 1)) (T * (secondWidth (r + 1 + 1) - 2) + 2),
      (∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (pieces (Aw t) (Ab t) x)) ∧
      net.HasRationalWeights ∧ net.HasRationalBiases ∧ (Ab = 0 → net.HasZeroBiases) := by
  obtain ⟨net, hnet, hout, hrow⟩ := caterpillar_sum_affine_rational r hr Aw Ab ε hε
  obtain ⟨hw, hb⟩ := Network.rational_of_outer hout
    (fun j i => by
      obtain ⟨t, h⟩ := hrow j
      exact h.weight_mem (fun a l => mem_ratField_iff.mpr (hAw t a l)) i)
    (fun j => by
      obtain ⟨t, h⟩ := hrow j
      exact h.bias_mem fun a => mem_ratField_iff.mpr (hAb t a))
  refine ⟨net, hnet, hw, hb, fun h0 => Network.zeroBiases_of_outer hout fun j => ?_⟩
  obtain ⟨t, h⟩ := hrow j
  exact h.bias_eq_zero (by rw [h0]; rfl)

/-! ## CPWL functions -/

/-- **CPWL functions, shared pieces, rational outer layers.** For `d ≥ 2`,
every `f ∈ CPWL d` has a Wang–Sun representation
`f = ∑ₜ εₜ max_{d+1}(g_{αₜ 0}, …, g_{αₜ d})` with `εₜ = ±1` and pairwise distinct
pieces `g_a` that all occur, and `f` is computed by a network of widths
`C(p,2) + p + 1` and `s · (secondWidth (d+1) - 2) + 2` whose second hidden
layer and output layer have rational weights and zero biases, and each of
whose first-layer neurons computes `g_a - g_b`, `g_a`, `-g_a`, or (only when
`p = 0`) zero. Version 2; Version 1 is `cpwl_two_hidden_layers_shared`. -/
theorem cpwl_two_hidden_layers_shared_rational (d : ℕ) (hd : 2 ≤ d) (f : Point d → ℝ)
    (hf : f ∈ MaxNN.CPWL d) :
    ∃ (p T : ℕ) (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ)
      (α : Fin T → Fin (d + 1) → Fin p) (ε : Fin T → ℝ),
      Function.Injective (fun a => (Gw a, Gb a)) ∧
      (∀ a, ∃ t i, α t i = a) ∧
      (∀ t, ε t = 1 ∨ ε t = -1) ∧
      (∀ x, f x = ∑ t, ε t *
        Maximum (d + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i))) ∧
      ∃ s : ℕ, s = (Finset.univ.image fun t => Finset.univ.image (α t)).card ∧ s ≤ T ∧
        ∃ net : Network d (p.choose 2 + p + 1) (s * (secondWidth (d + 1) - 2) + 2),
          (∀ x, net.eval x = f x) ∧ net.HasRationalOuterLayers ∧
          ∀ j, IsPieceRow Gw Gb (net.W₁ j) (net.b₁ j) ∨ (net.W₁ j = 0 ∧ net.b₁ j = 0) := by
  classical
  obtain ⟨T, ε, Aw, Ab, hε, hrep⟩ := wang_sun d f hf
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  -- Collect the distinct affine functions occurring in the representation.
  let S : Finset ((Fin (r + 1) → ℝ) × ℝ) :=
    Finset.univ.image fun ti : Fin T × Fin (r + 1 + 1) => (Aw ti.1 ti.2, Ab ti.1 ti.2)
  have hS : ∀ t i, (Aw t i, Ab t i) ∈ S := fun t i =>
    Finset.mem_image_of_mem (fun ti : Fin T × Fin (r + 1 + 1) => (Aw ti.1 ti.2, Ab ti.1 ti.2))
      (Finset.mem_univ (t, i))
  let e : S ≃ Fin S.card := S.equivFin
  let Gw : Fin S.card → Fin (r + 1) → ℝ := fun a => (e.symm a).1.1
  let Gb : Fin S.card → ℝ := fun a => (e.symm a).1.2
  let α : Fin T → Fin (r + 1 + 1) → Fin S.card := fun t i => e ⟨(Aw t i, Ab t i), hS t i⟩
  have hGw : ∀ t i, Gw (α t i) = Aw t i := fun t i => by
    show (e.symm (e _)).1.1 = _
    rw [Equiv.symm_apply_apply]
  have hGb : ∀ t i, Gb (α t i) = Ab t i := fun t i => by
    show (e.symm (e _)).1.2 = _
    rw [Equiv.symm_apply_apply]
  have hrep' : ∀ x, f x = ∑ t, ε t *
      Maximum (r + 1 + 1) (fun i => (∑ l, Gw (α t i) l * x l) + Gb (α t i)) := by
    intro x
    rw [hrep x]
    simp only [hGw, hGb]
  have hinj : Function.Injective (fun a => (Gw a, Gb a)) := by
    intro a b hab
    apply e.symm.injective
    exact Subtype.ext hab
  have hsurj : ∀ a, ∃ t i, α t i = a := by
    intro a
    obtain ⟨⟨t, i⟩, _, hti⟩ := Finset.mem_image.mp (e.symm a).2
    refine ⟨t, i, ?_⟩
    show e ⟨(Aw t i, Ab t i), hS t i⟩ = a
    rw [← e.apply_symm_apply a]
    exact congrArg e (Subtype.ext hti)
  have hεq : ∀ t, ∃ q : ℚ, (q : ℝ) = ε t := fun t => by
    rcases hε t with h | h
    · exact ⟨1, by rw [h, Rat.cast_one]⟩
    · exact ⟨-1, by rw [h, Rat.cast_neg, Rat.cast_one]⟩
  obtain ⟨net, hnet, hout, hrow⟩ :=
    caterpillar_shared_pieces_any_rational r (by omega) Gw Gb α ε hεq
  exact ⟨S.card, T, Gw, Gb, α, ε, hinj, hsurj, hε, hrep', _, rfl, card_imageSets_le α, net,
    fun x => (hnet x).trans (hrep' x).symm, hout, hrow⟩

end MaxCaterpillar
