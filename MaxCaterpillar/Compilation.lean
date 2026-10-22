import MaxCaterpillar.Construction
import MaxCaterpillar.Rationality

/-! # Coefficient-parametric compilation (Version 2)

Version 1 compiles the network only for the canonical inverse-Gram
coefficients (`network` in `Construction.lean`).  Version 2 separates the
network from its coefficients: any valid expansion

  `MAX = ∑_{k ∈ K} d_k U_k + R`,   `R` in the auxiliary span,

with retained units `U_k` whose inner hinges are coordinate differences,
compiles with the existing first hidden layer and `|K| + 2` second-layer
neurons.  All biases are zero, and the weights are rational whenever the
heads, the coefficients `d_k`, and the auxiliary coefficients of `R` are.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom

/-! ## Rational vectors -/

/-- Every entry of a real vector is rational. -/
def RatVec {m : ℕ} (v : Fin m → ℝ) : Prop := ∀ i, v i ∈ ratField

section RatVec

variable {m : ℕ} {v w : Fin m → ℝ}

theorem ratVec_zero : RatVec (0 : Fin m → ℝ) := fun _ => Subfield.zero_mem _

theorem RatVec.add (hv : RatVec v) (hw : RatVec w) : RatVec (v + w) :=
  fun i => Subfield.add_mem _ (hv i) (hw i)

theorem RatVec.sub (hv : RatVec v) (hw : RatVec w) : RatVec (v - w) :=
  fun i => Subfield.sub_mem _ (hv i) (hw i)

theorem RatVec.neg (hv : RatVec v) : RatVec (-v) :=
  fun i => Subfield.neg_mem _ (hv i)

theorem RatVec.smul {c : ℝ} (hc : c ∈ ratField) (hv : RatVec v) : RatVec (c • v) :=
  fun i => Subfield.mul_mem _ hc (hv i)

theorem ratVec_sum {ι : Type*} (s : Finset ι) {f : ι → Fin m → ℝ}
    (hf : ∀ i ∈ s, RatVec (f i)) : RatVec (∑ i in s, f i) := by
  intro j
  rw [Finset.sum_apply]
  exact sum_mem_ratField _ fun i hi => hf i hi j

theorem ratVec_delta (u : Fin m) : RatVec (fun k => if k = u then (1 : ℝ) else 0) := by
  intro k
  dsimp only
  split_ifs
  · exact Subfield.one_mem _
  · exact Subfield.zero_mem _

end RatVec

/-! ## Rationality of the compact layers -/

section Stack

variable {m n p : ℕ} (T : Affine m n) (S : Affine m p)

theorem stack_A_castAdd (i : Fin n) : (T.stack S).A (Fin.castAdd p i) = T.A i :=
  Fin.addCases_left (motive := fun _ => Fin m → ℝ) _
theorem stack_A_natAdd (i : Fin p) : (T.stack S).A (Fin.natAdd n i) = S.A i :=
  Fin.addCases_right (motive := fun _ => Fin m → ℝ) _
theorem stack_b_castAdd (i : Fin n) : (T.stack S).b (Fin.castAdd p i) = T.b i :=
  Fin.addCases_left (motive := fun _ => ℝ) _
theorem stack_b_natAdd (i : Fin p) : (T.stack S).b (Fin.natAdd n i) = S.b i :=
  Fin.addCases_right (motive := fun _ => ℝ) _

end Stack

section Compact

variable {n : ℕ}

theorem ratVec_compactUnitCoeff (u : Fin (compactWidth n)) :
    RatVec (compactUnitCoeff u) := ratVec_delta u

theorem ratVec_compactCoordCoeff (i : Fin (n + 1)) : RatVec (compactCoordCoeff i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold compactCoordCoeff
    rw [Fin.cases_zero]
    exact (ratVec_compactUnitCoeff _).sub (ratVec_compactUnitCoeff _)
  · unfold compactCoordCoeff
    rw [Fin.cases_succ]
    exact (((ratVec_compactUnitCoeff _).sub (ratVec_compactUnitCoeff _)).add
      (ratVec_compactUnitCoeff _)).sub (ratVec_compactUnitCoeff _)

theorem ratVec_compactHingeCoeff (a b : Fin (n + 1)) : RatVec (compactHingeCoeff a b) := by
  unfold compactHingeCoeff
  split_ifs
  · exact ratVec_compactUnitCoeff _
  · exact ((ratVec_compactCoordCoeff _).sub (ratVec_compactCoordCoeff _)).add
      (ratVec_compactUnitCoeff _)
  · exact ratVec_zero

theorem ratVec_compactRootHingeCoeff (v : Fin n → ℝ) :
    RatVec (compactRootHingeCoeff v) := by
  classical
  unfold compactRootHingeCoeff
  refine ratVec_sum _ fun p _ => ?_
  split_ifs
  · exact ratVec_compactHingeCoeff _ _
  · exact ratVec_zero

theorem ratVec_compactReducedLinearCoeff {γ : Fin n → ℝ} (hγ : RatVec γ) :
    RatVec (compactReducedLinearCoeff γ) := by
  unfold compactReducedLinearCoeff
  exact ratVec_sum _ fun i _ =>
    RatVec.smul (hγ i) ((ratVec_compactCoordCoeff _).sub (ratVec_compactCoordCoeff _))

theorem ratVec_compactRealUnitCoeff {k : RealKey n} (hk : RatVec k.1) :
    RatVec (compactRealUnitCoeff k) :=
  (ratVec_compactReducedLinearCoeff hk).add
    (ratVec_sum _ fun v _ => ratVec_compactRootHingeCoeff v)

theorem ratVec_compactOfPairCoeff {a : Fin (W (n + 1)) → ℝ} (ha : RatVec a) :
    RatVec (compactOfPairCoeff a) := by
  unfold compactOfPairCoeff
  exact (ratVec_sum _ fun i _ => RatVec.smul (ha _) (ratVec_compactCoordCoeff i)).add
    (ratVec_sum _ fun q _ => RatVec.smul (ha _) (ratVec_compactHingeCoeff _ _))

theorem ofCompact_W₁ (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ) (j : Fin (compactWidth n)) (i : Fin (n + 1)) :
    (ofCompact K c q).W₁ j i ∈ ratField := by
  change (compactFeatureLayer n).A j i ∈ ratField
  unfold compactFeatureLayer
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [stack_A_castAdd]
    unfold rootSignRows
    dsimp only
    split_ifs <;> first
      | exact Subfield.one_mem _
      | exact Subfield.zero_mem _
      | exact Subfield.neg_mem _ (Subfield.one_mem _)
      | exact Subfield.neg_mem _ (Subfield.zero_mem _)
  · rw [stack_A_natAdd]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [stack_A_castAdd]
      unfold reverseStarRows
      exact Subfield.sub_mem _ (ratVec_delta _ i) (ratVec_delta _ i)
    · rw [stack_A_natAdd]
      unfold pairRows
      exact Subfield.sub_mem _ (ratVec_delta _ i) (ratVec_delta _ i)

theorem ofCompact_W₂ (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    {q : Fin (W (n + 1)) → ℝ} (hq : RatVec q) (hK : ∀ k ∈ K, RatVec k.1)
    (k : Fin (K.card + 2)) (j : Fin (compactWidth n)) :
    (ofCompact K c q).W₂ k j ∈ ratField := by
  change (compactDictionarySecondLayer K (compactOfPairCoeff q)).A k j ∈ ratField
  unfold compactDictionarySecondLayer
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · rw [stack_A_castAdd]
    exact ratVec_compactRealUnitCoeff (hK _ (K.equivFin.symm k).2) j
  · rw [stack_A_natAdd]
    unfold compactRemainderRows
    dsimp only
    split_ifs
    · exact ratVec_compactOfPairCoeff hq j
    · exact (ratVec_compactOfPairCoeff hq).neg j

theorem ofCompact_w₃ (K : Finset (RealKey n)) {c : RealKey n → ℝ}
    (q : Fin (W (n + 1)) → ℝ) (hc : ∀ k ∈ K, c k ∈ ratField) (k : Fin (K.card + 2)) :
    (ofCompact K c q).w₃ k ∈ ratField := by
  change Fin.append (fun i => c (K.equivFin.symm i).1)
    (fun j : Fin 2 => if j = 0 then (1 : ℝ) else -1) k ∈ ratField
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · rw [Fin.append_left]
    exact hc _ (K.equivFin.symm k).2
  · rw [Fin.append_right]
    split_ifs
    · exact Subfield.one_mem _
    · exact Subfield.neg_mem _ (Subfield.one_mem _)

theorem ofCompact_hasZeroBiases (K : Finset (RealKey n)) (c : RealKey n → ℝ)
    (q : Fin (W (n + 1)) → ℝ) : (ofCompact K c q).HasZeroBiases := by
  refine ⟨?_, ?_, rfl⟩
  · funext j
    change (compactFeatureLayer n).b j = 0
    unfold compactFeatureLayer
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [stack_b_castAdd]; rfl
    · rw [stack_b_natAdd]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [stack_b_castAdd]; rfl
      · rw [stack_b_natAdd]; rfl
  · funext k
    change (compactDictionarySecondLayer K (compactOfPairCoeff q)).b k = 0
    unfold compactDictionarySecondLayer
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [stack_b_castAdd]; rfl
    · rw [stack_b_natAdd]; rfl

theorem ofCompact_hasRationalWeights (K : Finset (RealKey n)) {c : RealKey n → ℝ}
    {q : Fin (W (n + 1)) → ℝ} (hq : RatVec q) (hK : ∀ k ∈ K, RatVec k.1)
    (hc : ∀ k ∈ K, c k ∈ ratField) : (ofCompact K c q).HasRationalWeights :=
  ⟨fun j i => mem_ratField_iff.mp (ofCompact_W₁ K c q j i),
    fun k j => mem_ratField_iff.mp (ofCompact_W₂ K c hq hK k j),
    fun k => mem_ratField_iff.mp (ofCompact_w₃ K q hc k)⟩

end Compact

/-! ## Evaluation of an arbitrary expansion -/

section Expansion

variable {n : ℕ}

/-- The auxiliary span `A_N`: linear forms in `σ(x_i)`, `σ(-x_i)`, `σ(x_i - x_j)`. -/
noncomputable def auxiliary (a : Fin (W (n + 1)) → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, a j * feat (n + 1) x j

theorem auxiliary_diagonalEquivariant {K : Finset (RealKey n)} {d : RealKey n → ℝ}
    {a : Fin (W (n + 1)) → ℝ}
    (h : ∀ x, MAX (n + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x) :
    DiagonalEquivariant (auxiliary a) := by
  intro x t
  have hshift := h (fun i => x i + t)
  have hbase := h x
  rw [MaxNN.MAX_add_const] at hshift
  have hcorr : (∑ k in K, d k * realUnitY k (fun i => x i + t)) =
      ∑ k in K, d k * realUnitY k x :=
    Finset.sum_congr rfl fun k _ => by rw [realUnitY_add_const]
  rw [hcorr] at hshift
  linarith

/-- Version 2 compilation: any expansion with units `K` and an auxiliary
remainder is computed by `ofCompact K d a`, of second width `|K| + 2`. -/
theorem ofCompact_eval_of_expansion (K : Finset (RealKey n)) (d : RealKey n → ℝ)
    (a : Fin (W (n + 1)) → ℝ) (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (h : ∀ x, MAX (n + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x)
    (x : Fin (n + 1) → ℝ) :
    (ofCompact K d a).eval x = MAX (n + 1) x := by
  rw [ofCompact_eval]
  change (compactDictionaryNetwork K d (compactOfPairCoeff a)).eval x 0 = _
  rw [compactDictionaryNetwork_eval K d _ hK x,
    sum_compactOfPairCoeff_eq (f := auxiliary a) (fun _ => rfl)
      (auxiliary_diagonalEquivariant h) x, h x]

end Expansion

/-! ## Changing the declared widths -/

section Widths

variable {N h₁ h₁' h₂ : ℕ}

theorem Network.cast_first_eval (h : h₁ = h₁') (net : Network N h₁ h₂) (x : Point N) :
    (h ▸ net : Network N h₁' h₂).eval x = net.eval x := by
  subst h; rfl

theorem Network.cast_first_props (h : h₁ = h₁') (net : Network N h₁ h₂) :
    (net.HasRationalWeights → (h ▸ net : Network N h₁' h₂).HasRationalWeights) ∧
      (net.HasZeroBiases → (h ▸ net : Network N h₁' h₂).HasZeroBiases) := by
  subst h; exact ⟨id, id⟩

theorem Network.cast_second_eval {h₂' : ℕ} (h : h₂ = h₂') (net : Network N h₁ h₂)
    (x : Point N) : (h ▸ net : Network N h₁ h₂').eval x = net.eval x := by
  subst h; rfl

theorem Network.cast_second_props {h₂' : ℕ} (h : h₂ = h₂') (net : Network N h₁ h₂) :
    (net.HasRationalWeights → (h ▸ net : Network N h₁ h₂').HasRationalWeights) ∧
      (net.HasZeroBiases → (h ▸ net : Network N h₁ h₂').HasZeroBiases) := by
  subst h; exact ⟨id, id⟩

/-- Append `m` second-layer neurons with zero incoming and outgoing weights. -/
def Network.padSecond (m : ℕ) (net : Network N h₁ h₂) : Network N h₁ (h₂ + m) :=
  ⟨net.W₁, net.b₁, Fin.append net.W₂ (fun _ _ => 0), Fin.append net.b₂ (fun _ => 0),
    Fin.append net.w₃ (fun _ => 0), net.b₃⟩

theorem Network.padSecond_eval (m : ℕ) (net : Network N h₁ h₂) (x : Point N) :
    (net.padSecond m).eval x = net.eval x := by
  unfold Network.eval Network.padSecond
  dsimp only
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero]

theorem Network.padSecond_props (m : ℕ) (net : Network N h₁ h₂) :
    (net.HasRationalWeights → (net.padSecond m).HasRationalWeights) ∧
      (net.HasZeroBiases → (net.padSecond m).HasZeroBiases) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun k j => ?_, fun k => ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp only [Network.padSecond, Fin.append_left]; exact h2 k j
      · simp only [Network.padSecond, Fin.append_right]; exact ⟨0, Rat.cast_zero⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp only [Network.padSecond, Fin.append_left]; exact h3 k
      · simp only [Network.padSecond, Fin.append_right]; exact ⟨0, Rat.cast_zero⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Network.padSecond, Fin.append_left]; exact congrFun h2 k
    · simp only [Network.padSecond, Fin.append_right]; rfl

/-- Enlarge the second hidden layer to any larger declared width. -/
theorem Network.exists_widen {f : Point N → ℝ} (net : Network N h₁ h₂) {h₂' : ℕ}
    (hle : h₂ ≤ h₂') (hf : ∀ x, net.eval x = f x) :
    ∃ net' : Network N h₁ h₂', (∀ x, net'.eval x = f x) ∧
      (net.HasRationalWeights → net'.HasRationalWeights) ∧
      (net.HasZeroBiases → net'.HasZeroBiases) := by
  have he : h₂ + (h₂' - h₂) = h₂' := Nat.add_sub_cancel' hle
  refine ⟨he ▸ net.padSecond (h₂' - h₂), fun x => ?_, fun hr => ?_, fun hz => ?_⟩
  · rw [Network.cast_second_eval, Network.padSecond_eval, hf]
  · exact (Network.cast_second_props he _).1 ((Network.padSecond_props _ net).1 hr)
  · exact (Network.cast_second_props he _).2 ((Network.padSecond_props _ net).2 hz)

end Widths

/-! ## The compilation theorem -/

theorem compactWidth_eq_firstWidth (n : ℕ) : compactWidth n = firstWidth (n + 1) := by
  rw [compactWidth_eq]; rfl

/-- **Compilation theorem (Version 2).** Any expansion of the maximum by units
`K` with coordinate-difference inner hinges and an auxiliary remainder with
coefficient vector `a` is computed by a network with the first hidden layer of
`firstWidth` and `|K| + 2` second-layer neurons, zero biases, and rational
weights whenever the heads, `d`, and `a` are rational. -/
theorem compile_expansion {n : ℕ} (K : Finset (RealKey n)) (d : RealKey n → ℝ)
    (a : Fin (W (n + 1)) → ℝ) (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (h : ∀ x, MAX (n + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x) :
    ∃ net : Network (n + 1) (firstWidth (n + 1)) (K.card + 2),
      (∀ x, net.eval x = MAX (n + 1) x) ∧ net.HasZeroBiases ∧
      ((∀ k ∈ K, RatVec k.1) → (∀ k ∈ K, d k ∈ ratField) → RatVec a →
        net.HasRationalWeights) := by
  refine ⟨compactWidth_eq_firstWidth n ▸ ofCompact K d a, fun x => ?_, ?_, ?_⟩
  · rw [Network.cast_first_eval]
    exact ofCompact_eval_of_expansion K d a hK h x
  · exact (Network.cast_first_props _ _).2 (ofCompact_hasZeroBiases K d a)
  · intro hγ hd ha
    exact (Network.cast_first_props _ _).1 (ofCompact_hasRationalWeights K ha hγ hd)

/-- The same compilation, padded to any larger declared second width. -/
theorem compile_expansion_width {n h₂ : ℕ} (K : Finset (RealKey n)) (d : RealKey n → ℝ)
    (a : Fin (W (n + 1)) → ℝ) (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    (hγ : ∀ k ∈ K, RatVec k.1) (hd : ∀ k ∈ K, d k ∈ ratField) (ha : RatVec a)
    (h : ∀ x, MAX (n + 1) x = ∑ k in K, d k * realUnitY k x + auxiliary a x)
    (hle : K.card + 2 ≤ h₂) :
    ∃ net : Network (n + 1) (firstWidth (n + 1)) h₂,
      (∀ x, net.eval x = MAX (n + 1) x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases := by
  obtain ⟨net, heval, hz, hr⟩ := compile_expansion K d a hK h
  obtain ⟨net', h', hr', hz'⟩ := net.exists_widen hle heval
  exact ⟨net', h', hr' (hr hγ hd ha), hz' hz⟩

end MaxCaterpillar
