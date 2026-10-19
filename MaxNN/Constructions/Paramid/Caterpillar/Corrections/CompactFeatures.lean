import MaxNN.Constructions.Paramid.Caterpillar.Corrections.NetworkCoefficients

/-! # A compact first-layer feature dictionary

For inputs indexed by `Fin (n+1)`, keep one hinge for every unordered pair,
add the `n` reverse hinges `relu (x_{i+1}-x_0)`, and keep only the two signs
of the root coordinate.  The resulting width is
`(n+1).choose 2 + (n+1) + 1`.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidChain MaxNN.Width

variable {n : ℕ}

def compactWidth (n : ℕ) : ℕ := 2 + (n + (n + 1).choose 2)

theorem compactWidth_eq :
    compactWidth n = (n + 1).choose 2 + (n + 1) + 1 := by
  unfold compactWidth
  omega

noncomputable def rootSignRows (n : ℕ) : Affine (n + 1) 2 where
  A := fun j i => if j = 0 then (if i = 0 then 1 else 0)
    else -(if i = 0 then 1 else 0)
  b := fun _ => 0

theorem rootSignRows_eval_zero (x : Fin (n + 1) → ℝ) :
    (rootSignRows n).eval x 0 = x 0 := by
  unfold rootSignRows Affine.eval
  change (∑ j : Fin (n + 1),
    (if (0 : Fin 2) = 0 then (if j = 0 then 1 else 0)
      else -(if j = 0 then 1 else 0)) * x j) + 0 = x 0
  simp only [if_pos]
  rw [Affine.delta_row_sum (0 : Fin (n + 1)) x, add_zero]

theorem rootSignRows_eval_one (x : Fin (n + 1) → ℝ) :
    (rootSignRows n).eval x 1 = -(x 0) := by
  unfold rootSignRows Affine.eval
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  change (∑ j : Fin (n + 1),
    (if (1 : Fin 2) = 0 then (if j = 0 then 1 else 0)
      else -(if j = 0 then 1 else 0)) * x j) + 0 = -(x 0)
  simp only [if_neg h10]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib, Affine.delta_row_sum (0 : Fin (n + 1)) x, add_zero]

noncomputable def reverseStarRows (n : ℕ) : Affine (n + 1) n where
  A := fun i j => (if j = i.succ then 1 else 0) - (if j = 0 then 1 else 0)
  b := fun _ => 0

theorem reverseStarRows_eval (x : Fin (n + 1) → ℝ) (i : Fin n) :
    (reverseStarRows n).eval x i = x i.succ - x 0 := by
  unfold reverseStarRows Affine.eval
  rw [Finset.sum_congr rfl fun j _ => sub_mul
      (if j = i.succ then (1 : ℝ) else 0) (if j = 0 then (1 : ℝ) else 0) (x j),
    Finset.sum_sub_distrib, Affine.delta_row_sum i.succ x,
    Affine.delta_row_sum (0 : Fin (n + 1)) x, add_zero]

noncomputable def compactFeatureLayer (n : ℕ) : Affine (n + 1) (compactWidth n) :=
  (rootSignRows n).stack ((reverseStarRows n).stack (pairRows (n + 1)))

noncomputable def compactFeat (n : ℕ) (x : Fin (n + 1) → ℝ) :
    Fin (compactWidth n) → ℝ :=
  fun k => relu ((compactFeatureLayer n).eval x k)

def compactPosZeroIdx : Fin (compactWidth n) :=
  Fin.castAdd (n + (n + 1).choose 2) 0

def compactNegZeroIdx : Fin (compactWidth n) :=
  Fin.castAdd (n + (n + 1).choose 2) 1

def compactReverseIdx (i : Fin n) : Fin (compactWidth n) :=
  Fin.natAdd 2 (Fin.castAdd ((n + 1).choose 2) i)

def compactPairIdx (q : Fin ((n + 1).choose 2)) : Fin (compactWidth n) :=
  Fin.natAdd 2 (Fin.natAdd n q)

theorem compactFeat_pos_zero (x : Fin (n + 1) → ℝ) :
    compactFeat n x compactPosZeroIdx = relu (x 0) := by
  unfold compactFeat compactFeatureLayer compactPosZeroIdx
  rw [Affine.stack_eval_castAdd, rootSignRows_eval_zero]

theorem compactFeat_neg_zero (x : Fin (n + 1) → ℝ) :
    compactFeat n x compactNegZeroIdx = relu (-(x 0)) := by
  unfold compactFeat compactFeatureLayer compactNegZeroIdx
  rw [Affine.stack_eval_castAdd, rootSignRows_eval_one]

theorem compactFeat_reverse (x : Fin (n + 1) → ℝ) (i : Fin n) :
    compactFeat n x (compactReverseIdx i) = relu (x i.succ - x 0) := by
  unfold compactFeat compactFeatureLayer compactReverseIdx
  rw [Affine.stack_eval_natAdd, Affine.stack_eval_castAdd, reverseStarRows_eval]

theorem compactFeat_pair (x : Fin (n + 1) → ℝ)
    (q : Fin ((n + 1).choose 2)) :
    compactFeat n x (compactPairIdx q) =
      relu (x (prFst q) - x (prSnd q)) := by
  unfold compactFeat compactFeatureLayer compactPairIdx
  rw [Affine.stack_eval_natAdd, Affine.stack_eval_natAdd, pairRows_eval]

noncomputable def compactCoordLin (i : Fin (n + 1))
    (y : Fin (compactWidth n) → ℝ) : ℝ :=
  Fin.cases (y compactPosZeroIdx - y compactNegZeroIdx)
    (fun j => y compactPosZeroIdx - y compactNegZeroIdx +
      y (compactReverseIdx j) -
      y (compactPairIdx (prIdxOf 0 j.succ (Fin.succ_pos j)))) i

theorem compactCoordLin_feat (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    compactCoordLin i (compactFeat n x) = x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold compactCoordLin
    rw [Fin.cases_zero, compactFeat_pos_zero, compactFeat_neg_zero,
      relu_sub_relu_neg]
  · unfold compactCoordLin
    rw [Fin.cases_succ, compactFeat_pos_zero, compactFeat_neg_zero,
      compactFeat_reverse, compactFeat_pair,
      prFst_prIdxOf, prSnd_prIdxOf, relu_sub_relu_neg]
    rw [show x 0 - x j.succ = -(x j.succ - x 0) by ring]
    have hrelu := relu_sub_relu_neg (x j.succ - x 0)
    linarith

/-- Every oriented pair hinge is a linear form in the compact features. -/
noncomputable def compactHingeLin (a b : Fin (n + 1))
    (y : Fin (compactWidth n) → ℝ) : ℝ :=
  if h : a < b then y (compactPairIdx (prIdxOf a b h))
  else if h : b < a then
    compactCoordLin a y - compactCoordLin b y +
      y (compactPairIdx (prIdxOf b a h))
  else 0

theorem compactHingeLin_feat (x : Fin (n + 1) → ℝ) (a b : Fin (n + 1)) :
    compactHingeLin a b (compactFeat n x) = relu (x a - x b) := by
  unfold compactHingeLin
  by_cases hab : a < b
  · rw [dif_pos hab, compactFeat_pair, prFst_prIdxOf, prSnd_prIdxOf]
  · rw [dif_neg hab]
    by_cases hba : b < a
    · rw [dif_pos hba, compactCoordLin_feat, compactCoordLin_feat,
        compactFeat_pair, prFst_prIdxOf, prSnd_prIdxOf]
      have hrelu := relu_sub_relu_neg (x b - x a)
      rw [neg_sub] at hrelu
      linarith
    · have heq : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
      rw [dif_neg hba, heq, sub_self, relu_of_nonneg (le_refl 0)]

noncomputable def compactUnitCoeff (u : Fin (compactWidth n)) :
    Fin (compactWidth n) → ℝ :=
  fun k => if k = u then 1 else 0

theorem sum_compactUnitCoeff (u : Fin (compactWidth n))
    (y : Fin (compactWidth n) → ℝ) :
    ∑ k, compactUnitCoeff u k * y k = y u := by
  unfold compactUnitCoeff
  exact Affine.delta_row_sum u y

noncomputable def compactCoordCoeff (i : Fin (n + 1)) :
    Fin (compactWidth n) → ℝ :=
  Fin.cases
    (compactUnitCoeff compactPosZeroIdx - compactUnitCoeff compactNegZeroIdx)
    (fun j => compactUnitCoeff compactPosZeroIdx - compactUnitCoeff compactNegZeroIdx +
      compactUnitCoeff (compactReverseIdx j) -
      compactUnitCoeff (compactPairIdx (prIdxOf 0 j.succ (Fin.succ_pos j)))) i

theorem sum_compactCoordCoeff (i : Fin (n + 1))
    (y : Fin (compactWidth n) → ℝ) :
    ∑ k, compactCoordCoeff i k * y k = compactCoordLin i y := by
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold compactCoordCoeff compactCoordLin
    simp only [Fin.cases_zero, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
      sum_compactUnitCoeff]
  · unfold compactCoordCoeff compactCoordLin
    simp only [Fin.cases_succ, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_compactUnitCoeff]

noncomputable def compactHingeCoeff (a b : Fin (n + 1)) :
    Fin (compactWidth n) → ℝ :=
  if h : a < b then compactUnitCoeff (compactPairIdx (prIdxOf a b h))
  else if h : b < a then
    compactCoordCoeff a - compactCoordCoeff b +
      compactUnitCoeff (compactPairIdx (prIdxOf b a h))
  else 0

theorem sum_compactHingeCoeff (a b : Fin (n + 1))
    (y : Fin (compactWidth n) → ℝ) :
    ∑ k, compactHingeCoeff a b k * y k = compactHingeLin a b y := by
  unfold compactHingeCoeff compactHingeLin
  by_cases hab : a < b
  · simp only [dif_pos hab, sum_compactUnitCoeff]
  · simp only [dif_neg hab]
    by_cases hba : b < a
    · simp only [dif_pos hba, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib,
        sum_compactCoordCoeff, sum_compactUnitCoeff]
    · simp only [dif_neg hba, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- Literal compact coefficients for the hinge attached to a simplex difference. -/
noncomputable def compactRootHingeCoeff (v : Fin n → ℝ) :
    Fin (compactWidth n) → ℝ := by
  classical
  exact ∑ p : Fin (n + 1) × Fin (n + 1),
    if p.1 ≠ p.2 ∧ v = toR (vtx p.1) - toR (vtx p.2)
    then compactHingeCoeff p.1 p.2 else 0

theorem compactRootHingeCoeff_difference (a b : Fin (n + 1)) (hab : a ≠ b) :
    compactRootHingeCoeff (toR (vtx a) - toR (vtx b)) =
      compactHingeCoeff a b := by
  classical
  unfold compactRootHingeCoeff
  rw [Finset.sum_eq_single (a, b)]
  · rw [if_pos ⟨hab, rfl⟩]
  · intro p _ hp
    rw [if_neg]
    rintro ⟨_, he⟩
    obtain ⟨ha, hb⟩ := simplex_difference_endpoints hab he
    exact hp (Prod.ext ha.symm hb.symm)
  · intro hp
    exact False.elim (hp (Finset.mem_univ _))

theorem compactRootHingeCoeff_zero :
    compactRootHingeCoeff (0 : Fin n → ℝ) = 0 := by
  classical
  unfold compactRootHingeCoeff
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  rintro ⟨hne, he⟩
  have he' : toR (vtx p.1) - toR (vtx p.2) =
      toR (vtx p.1) - toR (vtx p.1) := by
    rw [← he, sub_self]
  have h := simplex_difference_endpoints hne he'
  exact hne h.2.symm

theorem sum_compactRootHingeCoeff (v : Fin n → ℝ)
    (hv : IsSimplexDifference v) (x : Fin (n + 1) → ℝ) :
    ∑ k, compactRootHingeCoeff v k * compactFeat n x k =
      relu (dot v ((CoordAux.coordT n).mulVec x)) := by
  obtain ⟨a, b, rfl⟩ := hv
  by_cases hab : a = b
  · subst b
    simp only [sub_self, compactRootHingeCoeff_zero, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, CoordAux.dot_zero_left, relu_of_nonneg (le_refl (0 : ℝ))]
  · rw [compactRootHingeCoeff_difference a b hab, sum_compactHingeCoeff,
      compactHingeLin_feat, SupportCut.dot_sub_left,
      dot_toR_vtx_coordT, dot_toR_vtx_coordT]
    congr 1
    ring

noncomputable def compactReducedLinearCoeff (γ : Fin n → ℝ) :
    Fin (compactWidth n) → ℝ :=
  ∑ i : Fin n, γ i •
    (compactCoordCoeff i.succ - compactCoordCoeff (0 : Fin (n + 1)))

theorem sum_compactReducedLinearCoeff (γ : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) :
    ∑ k, compactReducedLinearCoeff γ k * compactFeat n x k =
      dot γ ((CoordAux.coordT n).mulVec x) := by
  unfold compactReducedLinearCoeff
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm, CoordAux.coordT_mulVec]
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    sum_compactCoordCoeff, compactCoordLin_feat]

/-- Every actual correction-unit preactivation compiles to the compact layer. -/
noncomputable def compactRealUnitCoeff (k : RealKey n) :
    Fin (compactWidth n) → ℝ :=
  compactReducedLinearCoeff k.1 + ∑ v in k.2, compactRootHingeCoeff v

theorem sum_compactRealUnitCoeff (k : RealKey n)
    (hk : ∀ v ∈ k.2, IsSimplexDifference v) (x : Fin (n + 1) → ℝ) :
    ∑ j, compactRealUnitCoeff k j * compactFeat n x j = realUnitArg k x := by
  unfold compactRealUnitCoeff realUnitArg
  simp only [Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_add_distrib,
    sum_compactReducedLinearCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun v hv => sum_compactRootHingeCoeff v (hk v hv) x

/-- Functions with a literal linear readout from the compact first layer. -/
def CompactLin (n : ℕ) : Set ((Fin (n + 1) → ℝ) → ℝ) :=
  {f | ∃ a : Fin (compactWidth n) → ℝ,
    ∀ x, f x = ∑ k, a k * compactFeat n x k}

theorem zero_mem_compactLin : (fun _ : Fin (n + 1) → ℝ => (0 : ℝ)) ∈ CompactLin n := by
  refine ⟨fun _ => 0, fun x => ?_⟩
  simp only [zero_mul, Finset.sum_const_zero]

theorem add_mem_compactLin {f g : (Fin (n + 1) → ℝ) → ℝ}
    (hf : f ∈ CompactLin n) (hg : g ∈ CompactLin n) :
    (fun x => f x + g x) ∈ CompactLin n := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun k => a k + b k, fun x => ?_⟩
  change f x + g x = ∑ k, (a k + b k) * compactFeat n x k
  rw [ha x, hb x, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ =>
    (add_mul (a k) (b k) (compactFeat n x k)).symm

theorem smul_mem_compactLin {f : (Fin (n + 1) → ℝ) → ℝ}
    (c : ℝ) (hf : f ∈ CompactLin n) :
    (fun x => c * f x) ∈ CompactLin n := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k => c * a k, fun x => ?_⟩
  change c * f x = ∑ k, (c * a k) * compactFeat n x k
  rw [ha x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ =>
    (mul_assoc c (a k) (compactFeat n x k)).symm

theorem sum_mem_compactLin {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → (Fin (n + 1) → ℝ) → ℝ)
    (hf : ∀ i ∈ S, f i ∈ CompactLin n) :
    (fun x => ∑ i in S, f i x) ∈ CompactLin n := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero_mem_compactLin (n := n))
  | @insert i S hi ih =>
      have he : (fun x => ∑ j in insert i S, f j x) =
          fun x => f i x + ∑ j in S, f j x := by
        funext x
        rw [Finset.sum_insert hi]
      rw [he]
      exact add_mem_compactLin (hf i (Finset.mem_insert_self i S))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem coord_mem_compactLin (i : Fin (n + 1)) :
    (fun x : Fin (n + 1) → ℝ => x i) ∈ CompactLin n :=
  ⟨compactCoordCoeff i, fun x => by
    rw [sum_compactCoordCoeff, compactCoordLin_feat]⟩

theorem dot_coordT_mem_compactLin (γ : Fin n → ℝ) :
    (fun x : Fin (n + 1) → ℝ => dot γ ((CoordAux.coordT n).mulVec x)) ∈
      CompactLin n :=
  ⟨compactReducedLinearCoeff γ, fun x => (sum_compactReducedLinearCoeff γ x).symm⟩

theorem relu_dot_simplexDifference_mem_compactLin {v : Fin n → ℝ}
    (hv : IsSimplexDifference v) :
    (fun x : Fin (n + 1) → ℝ =>
      relu (dot v ((CoordAux.coordT n).mulVec x))) ∈ CompactLin n :=
  ⟨compactRootHingeCoeff v, fun x => (sum_compactRootHingeCoeff v hv x).symm⟩

theorem realUnitArg_mem_compactLin (k : RealKey n)
    (hk : ∀ v ∈ k.2, IsSimplexDifference v) :
    (fun x => realUnitArg k x) ∈ CompactLin n := by
  refine ⟨compactRealUnitCoeff k, fun x => (sum_compactRealUnitCoeff k hk x).symm⟩

/-- Correction-unit combinations whose remainder already uses the compact layer. -/
def CompactRealUnitSpan (n : ℕ) (K : Finset (RealKey n)) :
    Submodule ℝ ((Fin (n + 1) → ℝ) → ℝ) where
  carrier := {f | ∃ (c : RealKey n → ℝ) (r : (Fin (n + 1) → ℝ) → ℝ),
    r ∈ CompactLin n ∧ ∀ y, f y = ∑ k in K, c k * realUnitY k y + r y}
  zero_mem' := ⟨fun _ => 0, fun _ => 0, zero_mem_compactLin, fun y => by
    change (0 : ℝ) = ∑ k in K, 0 * realUnitY k y + 0
    simp only [zero_mul, Finset.sum_const_zero, zero_add]⟩
  add_mem' := by
    rintro f g ⟨c₁, r₁, hr₁, h₁⟩ ⟨c₂, r₂, hr₂, h₂⟩
    refine ⟨fun k => c₁ k + c₂ k, fun y => r₁ y + r₂ y,
      add_mem_compactLin hr₁ hr₂, fun y => ?_⟩
    change f y + g y =
      ∑ k in K, (c₁ k + c₂ k) * realUnitY k y + (r₁ y + r₂ y)
    rw [h₁ y, h₂ y,
      Finset.sum_congr rfl fun k _ => add_mul (c₁ k) (c₂ k) (realUnitY k y),
      Finset.sum_add_distrib]
    ring
  smul_mem' := by
    rintro a f ⟨c, r, hr, h⟩
    refine ⟨fun k => a * c k, fun y => a * r y, smul_mem_compactLin a hr, fun y => ?_⟩
    change a * f y = ∑ k in K, (a * c k) * realUnitY k y + a * r y
    rw [h y, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => (mul_assoc a (c k) (realUnitY k y)).symm

theorem compactRealUnitY_mem {K : Finset (RealKey n)} {k : RealKey n} (hk : k ∈ K) :
    (fun y => realUnitY k y) ∈ CompactRealUnitSpan n K := by
  refine ⟨fun k' => if k' = k then 1 else 0, fun _ => 0,
    zero_mem_compactLin, fun y => ?_⟩
  change realUnitY k y =
    ∑ k' in K, (if k' = k then 1 else 0) * realUnitY k' y + 0
  rw [add_zero, Finset.sum_eq_single k]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · exact fun hk' => absurd hk hk'

theorem compactLin_mem_realUnitSpan {K : Finset (RealKey n)}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : f ∈ CompactLin n) :
    f ∈ CompactRealUnitSpan n K := by
  refine ⟨fun _ => 0, f, hf, fun y => ?_⟩
  simp only [zero_mul, Finset.sum_const_zero, zero_add]

end MaxNN.Caterpillar.Corrections
