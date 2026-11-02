import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.SwitchingRows
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.Reindex
import MaxCaterpillar.Fiber.Count65.Paired.SwitchingPath
import MaxCaterpillar.Fiber.Count65.Paired.QuotientPaths

/-! Raw three-atom networks reach an actual switching profile, with the two
remaining physical neurons retained as arbitrary spectators. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
open BigOperators Absorption PairNormalization

noncomputable def switchingPrepared (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net) : Network 4 6 5 :=
  withSecondRows (normalizedAtomNetwork net) (switchingLiteralRows net U e)
    (normalizedAtomNetwork net).b₂

noncomputable def switchingProfileRows (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net)
    (q : Equiv.Perm (Fin 5)) : Fin 2 → Fin 6 → ℝ :=
  fun i => switchingLiteralRows net U e (q (Fin.natAdd 3 i))

noncomputable def switchingProfileWeights (net : Network 4 6 5)
    (q : Equiv.Perm (Fin 5)) : Fin 2 → ℝ :=
  fun i => (normalizedAtomNetwork net).w₃ (q (Fin.natAdd 3 i))

noncomputable def switchingProfile (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net)
    (q : Equiv.Perm (Fin 5)) : Network 4 6 5 :=
  switchingWithSpectators (pairedRows U) 0 (comparisonRow U)
    (atomOffsetRow net U (e 0)) (atomOffsetRow net U (e 1)) 0 0 0 0
    (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1)) (networkAtomFlip net (e 2))
    (switchingProfileRows net U e q) 0 (switchingProfileWeights net q) 0

private theorem physical_ext (a b : Network 4 6 5)
    (hA : a.W₁=b.W₁) (hβ : a.b₁=b.b₁) (hC : a.W₂=b.W₂)
    (hδ : a.b₂=b.b₂) (hd : a.w₃=b.w₃) (hθ : a.b₃=b.b₃) : a=b := by
  cases a
  cases b
  congr 1

private theorem switching_rows_prefix (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (e : Fin 3 ≃ NetworkAtoms net) (i : Fin 3) :
    switchingLiteralRows net U e (e i).val =
      (switchingTripleNet (pairedRows U) 0 (comparisonRow U)
        (atomOffsetRow net U (e 0)) (atomOffsetRow net U (e 1)) 0 0 0 0
        (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1))
        (networkAtomFlip net (e 2)) 0).W₂ i := by
  fin_cases i
  · change switchingLiteralRows net U e (e 0).val = _
    rw [switchingLiteralRows_first net U e 0 (by decide)]
    cases hflip : networkAtomFlip net (e 0)
    · simp only [hflip,if_true,if_false]
      funext j
      change comparisonRow U j-atomOffsetRow net U (e 0) j =
        comparisonRow U j+(0-1)*atomOffsetRow net U (e 0) j+0*atomOffsetRow net U (e 1) j
      ring
    · simp only [hflip,if_true,if_false]
      funext j
      change -(comparisonRow U j-atomOffsetRow net U (e 0) j) =
        -(comparisonRow U j+(0-1)*atomOffsetRow net U (e 0) j+0*atomOffsetRow net U (e 1) j)
      ring
  · change switchingLiteralRows net U e (e 1).val = _
    rw [switchingLiteralRows_first net U e 1 (by decide)]
    cases hflip : networkAtomFlip net (e 1)
    · simp only [hflip,if_true,if_false]
      funext j
      change comparisonRow U j-atomOffsetRow net U (e 1) j =
        comparisonRow U j+0*atomOffsetRow net U (e 0) j+(-1)*atomOffsetRow net U (e 1) j
      ring
    · simp only [hflip,if_true,if_false]
      funext j
      change -(comparisonRow U j-atomOffsetRow net U (e 1) j) =
        -(comparisonRow U j+0*atomOffsetRow net U (e 0) j+(-1)*atomOffsetRow net U (e 1) j)
      ring
  · change switchingLiteralRows net U e (e 2).val = _
    rw [switchingLiteralRows_third]
    unfold switchingThirdRow
    cases hflip : networkAtomFlip net (e 2)
    · simp only [hflip,if_true,if_false]
      funext j
      change comparisonRow U j-atomOffsetRow net U (e 0) j-atomOffsetRow net U (e 1) j =
        comparisonRow U j+(0-1)*atomOffsetRow net U (e 0) j+(-1)*atomOffsetRow net U (e 1) j
      ring
    · simp only [hflip,if_true,if_false]
      funext j
      change -(comparisonRow U j-atomOffsetRow net U (e 0) j-atomOffsetRow net U (e 1) j) =
        -(comparisonRow U j+(0-1)*atomOffsetRow net U (e 0) j+(-1)*atomOffsetRow net U (e 1) j)
      ring

/-- This is equality of every physical network parameter, not merely equality
of the realized function or a new identification in the symmetry quotient. -/
theorem switchingProfile_reindex (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (e : Fin 3 ≃ NetworkAtoms net) (q : Equiv.Perm (Fin 5))
    (hq : ∀ i : Fin 3,q (Fin.castAdd 2 i)=(e i).val)
    (hj : ∀ i,networkAtomJump net (e i)=(![1,1,-1] : Fin 3 → ℝ) i) :
    reindexSecond (switchingPrepared net U e) q = switchingProfile net U e q := by
  have hnb := normalizeAtoms_zeroBiases net 0 (networkAtomSlots net) hb
  change (normalizedAtomNetwork net).HasZeroBiases at hnb
  apply physical_ext
  · exact hU
  · exact hb.1
  · funext i
    refine Fin.addCases (m := 3) (n := 2)
      (motive := fun j => (reindexSecond (switchingPrepared net U e) q).W₂ j = (switchingProfile net U e q).W₂ j)
      (fun j => ?_) (fun j => ?_) i
    · change switchingLiteralRows net U e (q (Fin.castAdd 2 j)) =
        (Fin.append (switchingTripleNet (pairedRows U) 0 (comparisonRow U)
          (atomOffsetRow net U (e 0)) (atomOffsetRow net U (e 1)) 0 0 0 0
          (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1))
          (networkAtomFlip net (e 2)) 0).W₂ (switchingProfileRows net U e q)) (Fin.castAdd 2 j)
      rw [Fin.append_left,hq]
      exact switching_rows_prefix net U e j
    · change switchingLiteralRows net U e (q (Fin.natAdd 3 j)) =
        (Fin.append _ (switchingProfileRows net U e q)) (Fin.natAdd 3 j)
      rw [Fin.append_right]
      rfl
  · funext i
    change (normalizedAtomNetwork net).b₂ (q i) = _
    rw [hnb.2.1]
    refine Fin.addCases (m := 3) (n := 2)
      (motive := fun j => (0 : Fin 5 → ℝ) (q j) = (switchingProfile net U e q).b₂ j)
      (fun j => ?_) (fun j => ?_) i
    · change (0 : ℝ) = (Fin.append
        (switchingTripleNet (pairedRows U) 0 (comparisonRow U)
          (atomOffsetRow net U (e 0)) (atomOffsetRow net U (e 1)) 0 0 0 0
          (networkAtomFlip net (e 0)) (networkAtomFlip net (e 1))
          (networkAtomFlip net (e 2)) 0).b₂ (0 : Fin 2 → ℝ)) (Fin.castAdd 2 j)
      rw [Fin.append_left]
      fin_cases j
      · change (0 : ℝ) = if networkAtomFlip net (e 0) then
          -(0+(0-1)*0+0*0) else 0+(0-1)*0+0*0
        split_ifs <;> ring
      · change (0 : ℝ) = if networkAtomFlip net (e 1) then
          -(0+0*0+(-1)*0) else 0+0*0+(-1)*0
        split_ifs <;> ring
      · change (0 : ℝ) = if networkAtomFlip net (e 2) then
          -(0+(0-1)*0+(-1)*0) else 0+(0-1)*0+(-1)*0
        split_ifs <;> ring
    · change (0 : ℝ) = (Fin.append _ (0 : Fin 2 → ℝ)) (Fin.natAdd 3 j)
      rw [Fin.append_right]
      rfl
  · funext i
    refine Fin.addCases (m := 3) (n := 2)
      (motive := fun j => (reindexSecond (switchingPrepared net U e) q).w₃ j = (switchingProfile net U e q).w₃ j)
      (fun j => ?_) (fun j => ?_) i
    · change (normalizedAtomNetwork net).w₃ (q (Fin.castAdd 2 j)) =
        (Fin.append (![1,1,-1] : Fin 3 → ℝ) (switchingProfileWeights net q)) (Fin.castAdd 2 j)
      rw [Fin.append_left,hq,normalizedAtomNetwork_output,hj]
    · change (normalizedAtomNetwork net).w₃ (q (Fin.natAdd 3 j)) =
        (Fin.append _ (switchingProfileWeights net q)) (Fin.natAdd 3 j)
      rw [Fin.append_right]
      rfl
  · exact hb.2.2

/-- Both offset rows have zero comparison columns, even when the original
physical comparison coefficient is negative. -/
theorem atomOffsetRow_comparison_zero (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (i : NetworkAtoms net) :
    atomOffsetRow net U i 0=0 ∧ atomOffsetRow net U i 1=0 := by
  have hα := networkAtom_comparison_ne_zero net i
  have hβ : net.W₂ i.val 1= -net.W₂ i.val 0 := by
    linarith only [networkAtom_common_zero net i]
  simp [atomOffsetRow,unitAtomRow,comparisonRow,hα,hβ]

theorem switchingProfile_disjoint (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U≠0) (e : Fin 3 ≃ NetworkAtoms net)
    (hoff : ∀ a b,networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) :
    ∀ x,preact (pairedRows U) 0 (atomOffsetRow net U (e 0)) 0 x*
      preact (pairedRows U) 0 (atomOffsetRow net U (e 1)) 0 x=0 := by
  intro x
  rw [preact_pairedRows_zero,preact_pairedRows_zero]
  exact (three_atom_switching_offset_rows net U hcode e hoff).1 x

/-- Positive normalization and a literal incoming-row path, followed only by
an allowed physical permutation, give a path in the genuine full quotient. -/
theorem network_switching_profile (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hcode : codeDet U≠0)
    (hU : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (e : Fin 3 ≃ NetworkAtoms net)
    (hj : ∀ i,networkAtomJump net (e i)=(![1,1,-1] : Fin 3 → ℝ) i)
    (hoff : ∀ a b,networkAtomOffset net U a b (e 0)*networkAtomOffset net U a b (e 1)=0 ∧
      networkAtomOffset net U a b (e 2)=
        networkAtomOffset net U a b (e 0)+networkAtomOffset net U a b (e 1)) :
    ∃ (q : Equiv.Perm (Fin 5))
      (hprofile : ∀ x,(switchingProfile net U e q).eval x=Maximum 4 x),
      (∀ i : Fin 3,q (Fin.castAdd 2 i)=(e i).val) ∧
      Joined (quotientMk (⟨net,hnet⟩ : ExactFiber 4 6 5))
        (quotientMk (⟨switchingProfile net U e q,hprofile⟩ : ExactFiber 4 6 5)) := by
  obtain ⟨q,hq⟩ := three_atom_physical_permutation net e
  have hp := switchingLiteralRows_joinedIn_exact net U hcode hU hb hnet e hoff
  have heq := switchingProfile_reindex net U hU hb e q hq hj
  have hprofile : ∀ x,(switchingProfile net U e q).eval x=Maximum 4 x := by
    intro x
    rw [← heq,reindexSecond_eval]
    exact hp.target_mem x
  refine ⟨q,hprofile,hq,?_⟩
  let a : ExactFiber 4 6 5 := ⟨net,hnet⟩
  let b : ExactFiber 4 6 5 := ⟨switchingPrepared net U e,hp.target_mem⟩
  have hjoined := joinedIn_exact_quotient a b hp
  have hperm : quotientMk b=quotientMk (reindexSecondFiber q b) :=
    quotientMk_eq_of_step (SymmetryStep.hidden b (Equiv.refl _) q)
  have hbprofile : reindexSecondFiber q b =
      (⟨switchingProfile net U e q,hprofile⟩ : ExactFiber 4 6 5) := Subtype.ext heq
  rw [hperm,hbprofile] at hjoined
  exact hjoined

end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
