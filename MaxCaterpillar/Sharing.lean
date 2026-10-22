import MaxCaterpillar.Lemmas

/-! # Sharing caterpillar parts across a signed sum of maxima

By Wang--Sun, a CPWL function on `ℝᵈ` is a signed sum `∑ₜ εₜ max_{d+1} (Aₜ x)`;
by Koutschan--Moser--Ponomarchuk--Schicho (arXiv:2305.16933, Thm. 2.4) the
entries of the `Aₜ` can be taken among the affine constituents of `f`, and the
coefficients are integers. The statements below take the affine data as
input; the Wang--Sun theorem is formalized in `CPWL.lean`, the KMPS refinement
is not. Placing
`T` copies of a maximum network in parallel gives widths `T h₁` and `T h₂`.
This file proves that the second width can be reduced.

* `exists_network_sum_maximum`: given any pair-hinge expansion `E` of `max_N`
  with `m` retained units, and any first layer whose outputs linearly span
  every coordinate and every pair hinge `σ(yₛ i - yₛ j)` of every term, the
  signed sum is computed with second width `(#terms) * m + 2`: the `2 T`
  remainder neurons `σ(± Rₜ)` merge into one pair `σ(± ∑ₜ εₜ Rₜ)`.
* `exists_network_sum_affine_maximum`: arbitrary affine `Aₜ` (no shared
  pieces), first width `T * (C(N,2) + N + 1)`, second width `T m + 2`.
* `exists_network_shared_pieces`: the entries of all `Aₜ` are drawn from `p`
  affine pieces `g₀, …, g_{p-1}`. The first hidden layer is the paper's
  feature layer applied to `(g_a)_a`, of width `C(p,2) + p + 1`, independent of
  `T`. Terms whose index maps have the same image are merged, so the second
  width is `#{images} * m + 2`.
* `caterpillar_*`: the same with the Caterpillar Net expansion of
  `max_{r+2}`, where `m + 2 ≤ secondWidth (r + 2)`.
-/

open BigOperators

namespace MaxCaterpillar

/-! ## Pair-hinge expansions of the maximum -/

/-- A pair-hinge expansion of `max_N`: one coordinate, plus a signed sum of
units `σ(∑ⱼ V k j σ(y_{u j} - y_{v j}))` indexed by `ι`, plus a linear
combination of pair hinges. The paper's caterpillar expansion has this form
after the translation `y ↦ y - y₀ 𝟙` (`exists_caterpillarExpansion`). -/
structure PairExpansion (N : ℕ) [NeZero N] (ι φ : Type*) [Fintype ι] [Fintype φ] where
  i₀ : Fin N
  u : φ → Fin N
  v : φ → Fin N
  V : ι → φ → ℝ
  c : ι → ℝ
  q : φ → ℝ
  spec : ∀ y : Point N, Maximum N y = y i₀ +
    (∑ k, c k * relu (∑ j, V k j * relu (y (u j) - y (v j)))) +
    ∑ j, q j * relu (y (u j) - y (v j))

theorem relu_eq_maxnn : (relu : ℝ → ℝ) = MaxNN.relu := rfl

theorem relu_sub_relu_neg' (t : ℝ) : relu t - relu (-t) = t :=
  MaxNN.relu_sub_relu_neg t

/-! ## Assembling a network from finite index types -/

theorem exists_network_of_families {d : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (W₁ : ι₁ → Fin d → ℝ) (b₁ : ι₁ → ℝ) (W₂ : ι₂ → ι₁ → ℝ) (b₂ : ι₂ → ℝ)
    (w₃ : ι₂ → ℝ) (b₃ : ℝ) :
    ∃ net : Network d (Fintype.card ι₁) (Fintype.card ι₂), ∀ x, net.eval x =
      (∑ k, w₃ k * relu ((∑ j, W₂ k j * relu ((∑ i, W₁ j i * x i) + b₁ j)) + b₂ k))
        + b₃ := by
  classical
  let e₁ := Fintype.equivFin ι₁
  let e₂ := Fintype.equivFin ι₂
  refine ⟨⟨fun j => W₁ (e₁.symm j), fun j => b₁ (e₁.symm j),
    fun k j => W₂ (e₂.symm k) (e₁.symm j), fun k => b₂ (e₂.symm k),
    fun k => w₃ (e₂.symm k), b₃⟩, fun x => ?_⟩
  have h : ∀ k', (∑ j, W₂ k' (e₁.symm j) *
      relu ((∑ i, W₁ (e₁.symm j) i * x i) + b₁ (e₁.symm j))) =
      ∑ j, W₂ k' j * relu ((∑ i, W₁ j i * x i) + b₁ j) := fun k' =>
    e₁.symm.sum_comp (fun j => W₂ k' j * relu ((∑ i, W₁ j i * x i) + b₁ j))
  simp only [Network.eval, h]
  rw [e₂.symm.sum_comp (fun k => w₃ k *
    relu ((∑ j, W₂ k j * relu ((∑ i, W₁ j i * x i) + b₁ j)) + b₂ k))]

/-! ## Linear readouts of a first hidden layer -/

section Readout

variable {d : ℕ} {ι₁ : Type*} [Fintype ι₁]

/-- The linear readout `∑ₗ κₗ σ(W₁ₗ · x + b₁ₗ)` of a first hidden layer. -/
noncomputable def readout (W₁ : ι₁ → Fin d → ℝ) (b₁ : ι₁ → ℝ) (κ : ι₁ → ℝ)
    (x : Point d) : ℝ :=
  ∑ l, κ l * relu ((∑ i, W₁ l i * x i) + b₁ l)

variable (W₁ : ι₁ → Fin d → ℝ) (b₁ : ι₁ → ℝ) (x : Point d)

theorem readout_add (κ κ' : ι₁ → ℝ) :
    readout W₁ b₁ (κ + κ') x = readout W₁ b₁ κ x + readout W₁ b₁ κ' x := by
  unfold readout
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem readout_smul (a : ℝ) (κ : ι₁ → ℝ) :
    readout W₁ b₁ (a • κ) x = a * readout W₁ b₁ κ x := by
  unfold readout
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem readout_neg (κ : ι₁ → ℝ) :
    readout W₁ b₁ (-κ) x = -readout W₁ b₁ κ x := by
  unfold readout
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem readout_sum {α : Type*} (s : Finset α) (κ : α → ι₁ → ℝ) :
    readout W₁ b₁ (∑ a in s, κ a) x = ∑ a in s, readout W₁ b₁ (κ a) x := by
  unfold readout
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

end Readout

/-! ## The core sharing theorem -/

/-- **Merged remainder.** Let `E` be a pair-hinge expansion of `max_N` with
retained units indexed by `ι`. Let the first hidden layer `(W₁, b₁)`, indexed
by `ι₁`, linearly span every coordinate `yₛ(x)ᵢ` and every pair hinge
`σ(yₛ(x)ᵢ - yₛ(x)ⱼ)` of every term `s : τ`. Then `∑ₛ eₛ max_N(yₛ x)` is
computed with first width `|ι₁|` and second width `|τ| |ι| + 2`: one copy of
the retained units per term, and a single pair `σ(±R)` for the combined
remainder `R = ∑ₛ eₛ Rₛ`. -/
theorem exists_network_sum_maximum {d N : ℕ} [NeZero N]
    {ι φ ι₁ τ : Type*} [Fintype ι] [Fintype φ] [Fintype ι₁] [Fintype τ]
    (E : PairExpansion N ι φ)
    (W₁ : ι₁ → Fin d → ℝ) (b₁ : ι₁ → ℝ) (y : τ → Point d → Point N) (e : τ → ℝ)
    (hcoord : ∀ s i, ∃ κ : ι₁ → ℝ, ∀ x,
      ∑ l, κ l * relu ((∑ i', W₁ l i' * x i') + b₁ l) = y s x i)
    (hhinge : ∀ s i j, ∃ κ : ι₁ → ℝ, ∀ x,
      ∑ l, κ l * relu ((∑ i', W₁ l i' * x i') + b₁ l) = relu (y s x i - y s x j)) :
    ∃ net : Network d (Fintype.card ι₁) (Fintype.card τ * Fintype.card ι + 2),
      ∀ x, net.eval x = ∑ s, e s * Maximum N (y s x) := by
  classical
  choose κC hκC using hcoord
  choose κH hκH using hhinge
  obtain ⟨row, hrow_def⟩ : ∃ row : τ × ι → ι₁ → ℝ,
      row = fun p => ∑ j, E.V p.2 j • κH p.1 (E.u j) (E.v j) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ι₁ → ℝ,
      ρ = ∑ s, e s • (κC s E.i₀ + ∑ j, E.q j • κH s (E.u j) (E.v j)) := ⟨_, rfl⟩
  let W₂ : (τ × ι) ⊕ Fin 2 → ι₁ → ℝ :=
    Sum.elim row (fun m => if m = 0 then ρ else -ρ)
  let w₃ : (τ × ι) ⊕ Fin 2 → ℝ :=
    Sum.elim (fun p => e p.1 * E.c p.2) (fun m => if m = 0 then 1 else -1)
  have hcard : Fintype.card ((τ × ι) ⊕ Fin 2) =
      Fintype.card τ * Fintype.card ι + 2 := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [← hcard]
  obtain ⟨net, hnet⟩ := exists_network_of_families W₁ b₁ W₂ (fun _ => 0) w₃ 0
  refine ⟨net, fun x => ?_⟩
  rw [hnet x, add_zero]
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

/-! ## The paper's feature layer applied to affine pieces -/

section Pieces

open MaxNN.Caterpillar.Corrections

/-- The affine pieces `g_a(x) = ∑ₗ Gw a l xₗ + Gb a`. -/
noncomputable def pieces {d p : ℕ} (Gw : Fin p → Fin d → ℝ) (Gb : Fin p → ℝ)
    (x : Point d) : Fin p → ℝ :=
  fun a => (∑ l, Gw a l * x l) + Gb a

/-- First-layer weights of `Φ ∘ g`, where `Φ` is the feature layer of the paper. -/
noncomputable def piecesW₁ {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ) :
    Fin (compactWidth n) → Fin d → ℝ :=
  fun j i => ∑ a, (compactFeatureLayer n).A j a * Gw a i

noncomputable def piecesb₁ {n : ℕ} (Gb : Fin (n + 1) → ℝ) : Fin (compactWidth n) → ℝ :=
  fun j => (∑ a, (compactFeatureLayer n).A j a * Gb a) + (compactFeatureLayer n).b j

theorem piecesW₁_pre {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (x : Point d) (j : Fin (compactWidth n)) :
    (∑ i, piecesW₁ Gw j i * x i) + piecesb₁ Gb j =
      (compactFeatureLayer n).eval (pieces Gw Gb x) j := by
  unfold piecesW₁ piecesb₁ pieces MaxNN.Affine.eval
  simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  ring

theorem piecesW₁_readout {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (κ : Fin (compactWidth n) → ℝ) (x : Point d) :
    ∑ j, κ j * relu ((∑ i, piecesW₁ Gw j i * x i) + piecesb₁ Gb j) =
      ∑ j, κ j * compactFeat n (pieces Gw Gb x) j := by
  simp only [piecesW₁_pre]
  rfl

theorem pieces_coord_span {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (a : Fin (n + 1)) : ∃ κ : Fin (compactWidth n) → ℝ, ∀ x,
      ∑ j, κ j * relu ((∑ i, piecesW₁ Gw j i * x i) + piecesb₁ Gb j) = pieces Gw Gb x a :=
  ⟨compactCoordCoeff a, fun x => by
    rw [piecesW₁_readout, sum_compactCoordCoeff, compactCoordLin_feat]⟩

theorem pieces_hinge_span {d n : ℕ} (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (a b : Fin (n + 1)) : ∃ κ : Fin (compactWidth n) → ℝ, ∀ x,
      ∑ j, κ j * relu ((∑ i, piecesW₁ Gw j i * x i) + piecesb₁ Gb j) =
        relu (pieces Gw Gb x a - pieces Gw Gb x b) :=
  ⟨compactHingeCoeff a b, fun x => by
    rw [piecesW₁_readout, sum_compactHingeCoeff, compactHingeLin_feat]
    rfl⟩

end Pieces

/-! ## The maximum depends only on the set of its arguments -/

theorem maximum_comp_le {N p : ℕ} [NeZero N] (g : Fin p → ℝ) (α β : Fin N → Fin p)
    (h : Finset.univ.image α ⊆ Finset.univ.image β) :
    Maximum N (fun i => g (α i)) ≤ Maximum N (fun i => g (β i)) := by
  rw [Internal.maximum_eq_MAX]
  refine MaxNN.MAX_le fun i => ?_
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (h (Finset.mem_image_of_mem α (Finset.mem_univ i)))
  rw [← hj]
  exact MaxNN.le_MAX N (fun i => g (β i)) j

theorem maximum_comp_eq {N p : ℕ} [NeZero N] (g : Fin p → ℝ) (α β : Fin N → Fin p)
    (h : Finset.univ.image α = Finset.univ.image β) :
    Maximum N (fun i => g (α i)) = Maximum N (fun i => g (β i)) :=
  le_antisymm (maximum_comp_le g α β h.le) (maximum_comp_le g β α h.ge)

/-! ## Shared affine pieces -/

/-- The set of argument sets `{α t i : i}` of the terms. -/
def imageSets {N p T : ℕ} (α : Fin T → Fin N → Fin p) : Finset (Finset (Fin p)) :=
  Finset.univ.image fun t => Finset.univ.image (α t)

open MaxNN.Caterpillar.Corrections in
/-- **Shared pieces.** If every term is `max_N` of `N` of the affine pieces
`g₀, …, g_n`, the first hidden layer `Φ ∘ g` of width `C(n+1,2) + (n+1) + 1`
serves all terms, and all terms with the same argument set share their
retained second-layer units. -/
theorem exists_network_shared_pieces {d N n T : ℕ} [NeZero N]
    {ι φ : Type*} [Fintype ι] [Fintype φ] (E : PairExpansion N ι φ)
    (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (α : Fin T → Fin N → Fin (n + 1)) (ε : Fin T → ℝ) :
    ∃ net : Network d ((n + 1).choose 2 + (n + 1) + 1)
      ((imageSets α).card * Fintype.card ι + 2),
      ∀ x, net.eval x = ∑ t, ε t * Maximum N (fun i => pieces Gw Gb x (α t i)) := by
  classical
  have hrep : ∀ S : imageSets α, ∃ t, Finset.univ.image (α t) = S.1 := fun S => by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp S.2
    exact ⟨t, ht⟩
  choose rep hrep using hrep
  let e : imageSets α → ℝ := fun S =>
    ∑ t in Finset.univ.filter (fun t => Finset.univ.image (α t) = S.1), ε t
  rw [show (n + 1).choose 2 + (n + 1) + 1 = Fintype.card (Fin (compactWidth n)) by
      rw [Fintype.card_fin, compactWidth_eq],
    show (imageSets α).card = Fintype.card (imageSets α) from (Fintype.card_coe _).symm]
  obtain ⟨net, hnet⟩ := exists_network_sum_maximum E (piecesW₁ Gw) (piecesb₁ Gb)
    (fun S x i => pieces Gw Gb x (α (rep S) i)) e
    (fun S _ => pieces_coord_span Gw Gb _) (fun S _ _ => pieces_hinge_span Gw Gb _ _)
  refine ⟨net, fun x => ?_⟩
  rw [hnet x, ← Finset.sum_fiberwise_of_maps_to (t := imageSets α)
    (g := fun t => Finset.univ.image (α t))
    (fun t _ => Finset.mem_image_of_mem _ (Finset.mem_univ t)),
    ← Finset.sum_coe_sort (imageSets α)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [maximum_comp_eq (pieces Gw Gb x) (α t) (α (rep S))
    ((Finset.mem_filter.mp ht).2.trans (hrep S).symm)]

theorem card_imageSets_le {N p T : ℕ} (α : Fin T → Fin N → Fin p) :
    (imageSets α).card ≤ T :=
  Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])

/-- With exactly `N` distinct pieces in every term, there are at most
`C(p, N)` argument sets. -/
theorem card_imageSets_le_choose {N p T : ℕ} (α : Fin T → Fin N → Fin p)
    (hα : ∀ t, Function.Injective (α t)) :
    (imageSets α).card ≤ p.choose N := by
  classical
  have hsub : imageSets α ⊆ (Finset.univ : Finset (Fin p)).powersetCard N := by
    intro S hS
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (hα t), Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_of_subset hsub
  rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this

/-! ## Arbitrary affine maps: one feature block per term -/

theorem sum_block {T : ℕ} {β : Type*} [Fintype β] (F : Fin T × β → ℝ) (t : Fin T)
    (κ₀ : β → ℝ) :
    ∑ p : Fin T × β, (if p.1 = t then κ₀ p.2 else 0) * F p = ∑ j, κ₀ j * F (t, j) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
  · simp only [if_pos rfl, ite_true]
  · intro b _ hb
    simp only [if_neg hb, zero_mul, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

open MaxNN.Caterpillar.Corrections in
/-- **Merged remainder, no shared pieces.** For arbitrary affine maps
`Aₜ x = Awₜ x + Abₜ`, the signed sum `∑ₜ εₜ max_{n+1}(Aₜ x)` is computed with
`T` blocks of the paper's first hidden layer and second width
`T |ι| + 2` instead of `T (|ι| + 2)`. -/
theorem exists_network_sum_affine_maximum {d n T : ℕ}
    {ι φ : Type*} [Fintype ι] [Fintype φ] (E : PairExpansion (n + 1) ι φ)
    (Aw : Fin T → Fin (n + 1) → Fin d → ℝ) (Ab : Fin T → Fin (n + 1) → ℝ)
    (ε : Fin T → ℝ) :
    ∃ net : Network d (T * ((n + 1).choose 2 + (n + 1) + 1)) (T * Fintype.card ι + 2),
      ∀ x, net.eval x = ∑ t, ε t * Maximum (n + 1) (pieces (Aw t) (Ab t) x) := by
  classical
  rw [show T * ((n + 1).choose 2 + (n + 1) + 1) =
      Fintype.card (Fin T × Fin (compactWidth n)) by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, compactWidth_eq]]
  have h := exists_network_sum_maximum E
    (fun p : Fin T × Fin (compactWidth n) => piecesW₁ (Aw p.1) p.2)
    (fun p => piecesb₁ (Ab p.1) p.2) (fun t x => pieces (Aw t) (Ab t) x) ε
    (fun t i => by
      obtain ⟨κ₀, hκ₀⟩ := pieces_coord_span (Aw t) (Ab t) i
      exact ⟨fun p => if p.1 = t then κ₀ p.2 else 0, fun x => by
        rw [sum_block (fun p : Fin T × Fin (compactWidth n) =>
          relu ((∑ i', piecesW₁ (Aw p.1) p.2 i' * x i') + piecesb₁ (Ab p.1) p.2))]
        exact hκ₀ x⟩)
    (fun t i j => by
      obtain ⟨κ₀, hκ₀⟩ := pieces_hinge_span (Aw t) (Ab t) i j
      exact ⟨fun p => if p.1 = t then κ₀ p.2 else 0, fun x => by
        rw [sum_block (fun p : Fin T × Fin (compactWidth n) =>
          relu ((∑ i', piecesW₁ (Aw p.1) p.2 i' * x i') + piecesb₁ (Ab p.1) p.2))]
        exact hκ₀ x⟩)
  rwa [Fintype.card_fin] at h

/-! ## The Caterpillar Net as a pair-hinge expansion -/

section Caterpillar

open MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.Width

/-- After `y ↦ y - y₀ 𝟙`, the feature `j` of the paper's first hidden layer
is `σ(y_{u j} - y_{v j})`; these are its two indices. -/
noncomputable def featurePair (n : ℕ) (j : Fin (compactWidth n)) : Fin (n + 1) × Fin (n + 1) :=
  Fin.addCases (m := 2) (n := n + (n + 1).choose 2) (fun _ => (0, 0))
    (fun b => Fin.addCases (m := n) (n := (n + 1).choose 2) (fun i => (i.succ, 0))
      (fun q => (prFst q, prSnd q)) b) j

theorem compactFeat_sub_root (n : ℕ) (y : Fin (n + 1) → ℝ) (j : Fin (compactWidth n)) :
    compactFeat n (fun i => y i - y 0) j =
      relu (y (featurePair n j).1 - y (featurePair n j).2) := by
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ : (∃ a : Fin 2, j = Fin.castAdd _ a) ∨
      ∃ b : Fin (n + (n + 1).choose 2), j = Fin.natAdd 2 b :=
    Fin.addCases (m := 2) (n := n + (n + 1).choose 2)
      (motive := fun j => (∃ a : Fin 2, j = Fin.castAdd _ a) ∨
        ∃ b : Fin (n + (n + 1).choose 2), j = Fin.natAdd 2 b)
      (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) j
  · unfold featurePair
    rw [Fin.addCases_left]
    fin_cases a
    · show compactFeat n _ compactPosZeroIdx = _
      rw [compactFeat_pos_zero]
      rfl
    · show compactFeat n _ compactNegZeroIdx = _
      rw [compactFeat_neg_zero]
      simp only [sub_self, neg_zero]
      rfl
  · unfold featurePair
    rw [Fin.addCases_right]
    obtain ⟨i, rfl⟩ | ⟨q, rfl⟩ : (∃ i : Fin n, b = Fin.castAdd _ i) ∨
        ∃ q : Fin ((n + 1).choose 2), b = Fin.natAdd n q :=
      Fin.addCases (m := n) (n := (n + 1).choose 2)
        (motive := fun b => (∃ i : Fin n, b = Fin.castAdd _ i) ∨
          ∃ q : Fin ((n + 1).choose 2), b = Fin.natAdd n q)
        (fun i => Or.inl ⟨i, rfl⟩) (fun q => Or.inr ⟨q, rfl⟩) b
    · rw [Fin.addCases_left]
      show compactFeat n _ (compactReverseIdx i) = _
      rw [compactFeat_reverse]
      show MaxNN.relu _ = MaxNN.relu _
      congr 1
      ring
    · rw [Fin.addCases_right]
      show compactFeat n _ (compactPairIdx q) = _
      rw [compactFeat_pair]
      show MaxNN.relu _ = MaxNN.relu _
      congr 1
      ring

/-- The retained keys of the Caterpillar Net for `max_{r+2}`. -/
noncomputable abbrev caterpillarKeys (r : ℕ) : Finset (RealKey (r + 1)) :=
  essentialKeys (Canonical.canonicalActiveKeys r)

theorem card_caterpillarKeys_le (r : ℕ) (hr : 1 ≤ r) :
    (caterpillarKeys r).card + 2 ≤ secondWidth (r + 1 + 1) := by
  have h := essentialSecondWidth_le_of_cone_bound r _ hr (normalized_cone_count r)
  rw [Internal.secondWidth_eq, ← Internal.coneCount_eq_spineConeBound]
  exact h

/-- The Caterpillar Net, written as a pair-hinge expansion of `max_{r+2}`
with one retained unit per key; the two remainder neurons are not counted. -/
theorem exists_caterpillarExpansion (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (PairExpansion (r + 1 + 1) (caterpillarKeys r) (Fin (compactWidth (r + 1)))) := by
  classical
  set K := caterpillarKeys r
  let c := Canonical.canonicalNormalizedCoeff r
  let q := compactOfPairCoeff (absorbedRemainderCoeff (Canonical.canonicalActiveKeys r)
    (Canonical.canonicalNormalizedCoeff r) (Canonical.canonicalRemainderCoeff r))
  have hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v :=
    essentialKeys_labels _ fun k hk => normalizedKeys_simplexDifference k (Finset.mem_filter.mp hk).1
  have hmax : ∀ x, MaxNN.MAX (r + 1 + 1) x =
      ∑ k in K, c k * realUnitY k x + ∑ j, q j * compactFeat (r + 1) x j := fun x =>
    (compactEssentialNetwork_computes r hr x).symm.trans
      (compactDictionaryNetwork_eval K c q hK x)
  refine ⟨⟨0, fun j => (featurePair (r + 1) j).1, fun j => (featurePair (r + 1) j).2,
    fun k j => compactRealUnitCoeff k.1 j, fun k => c k.1, q, fun y => ?_⟩⟩
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

theorem network_mono_right {d h₁ h₂ h₂' : ℕ} {f : Point d → ℝ} (h : h₂ ≤ h₂')
    (hf : ∃ net : Network d h₁ h₂, ∀ x, net.eval x = f x) :
    ∃ net : Network d h₁ h₂', ∀ x, net.eval x = f x :=
  Internal.twoLayerWidth_iff.mp ((Internal.twoLayerWidth_iff.mpr hf).mono_right h)

/-- **Caterpillar Net, shared affine pieces.** Let `g₀, …, g_n` be affine
pieces on `ℝᵈ`, and `f = ∑ₜ εₜ max_{r+2}(g_{αₜ 0}, …, g_{αₜ (r+1)})`. Then `f`
has a network with first width `C(n+1,2) + (n+1) + 1` and second width
`s (h₂ - 2) + 2`, where `s` is the number of distinct argument sets and
`h₂ = secondWidth (r+2)`. -/
theorem caterpillar_shared_pieces {d n T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin (n + 1)) (ε : Fin T → ℝ) :
    ∃ net : Network d ((n + 1).choose 2 + (n + 1) + 1)
      ((imageSets α).card * (secondWidth (r + 1 + 1) - 2) + 2),
      ∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (fun i => pieces Gw Gb x (α t i)) := by
  obtain ⟨E⟩ := exists_caterpillarExpansion r hr
  have hK := card_caterpillarKeys_le r hr
  refine network_mono_right ?_ (exists_network_shared_pieces E Gw Gb α ε)
  rw [Fintype.card_coe]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2

/-- The same, with exactly `r + 2` distinct pieces in every term: the second
width is at most `min(T, C(n+1, r+2)) (h₂ - 2) + 2`. -/
theorem caterpillar_shared_pieces_min {d n T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Gw : Fin (n + 1) → Fin d → ℝ) (Gb : Fin (n + 1) → ℝ)
    (α : Fin T → Fin (r + 1 + 1) → Fin (n + 1)) (hα : ∀ t, Function.Injective (α t))
    (ε : Fin T → ℝ) :
    ∃ net : Network d ((n + 1).choose 2 + (n + 1) + 1)
      (min T ((n + 1).choose (r + 1 + 1)) * (secondWidth (r + 1 + 1) - 2) + 2),
      ∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (fun i => pieces Gw Gb x (α t i)) :=
  network_mono_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right _
      (le_min (card_imageSets_le α) (card_imageSets_le_choose α hα))) 2)
    (caterpillar_shared_pieces r hr Gw Gb α ε)

/-- **Caterpillar Net, arbitrary affine maps.** For `f = ∑ₜ εₜ max_N(Aₜ x)`
with `N = r + 2` and arbitrary affine `Aₜ : ℝᵈ → ℝᴺ`, there is a network
with first width `T h₁` and second width `T (h₂ - 2) + 2`, where `(h₁, h₂)`
are the widths of the Caterpillar Net for `max_N`. -/
theorem caterpillar_sum_affine {d T : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (Aw : Fin T → Fin (r + 1 + 1) → Fin d → ℝ) (Ab : Fin T → Fin (r + 1 + 1) → ℝ)
    (ε : Fin T → ℝ) :
    ∃ net : Network d (T * firstWidth (r + 1 + 1)) (T * (secondWidth (r + 1 + 1) - 2) + 2),
      ∀ x, net.eval x = ∑ t, ε t * Maximum (r + 1 + 1) (pieces (Aw t) (Ab t) x) := by
  obtain ⟨E⟩ := exists_caterpillarExpansion r hr
  have hK := card_caterpillarKeys_le r hr
  refine network_mono_right ?_ (exists_network_sum_affine_maximum E Aw Ab ε)
  rw [Fintype.card_coe]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2

end Caterpillar

end MaxCaterpillar

