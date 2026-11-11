import MaxCaterpillar.Frontier.RandomRestriction.BraidModelChamber
import MaxCaterpillar.Frontier.RandomRestriction.BraidModelQuadratic
import MaxCaterpillar.Frontier.StarCertificate.MobiusObstruction
import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphQuadratic

/-! # From actual normalized braid networks to the Möbius obstruction

Every original first and second neuron index is retained. Both feeding and
output-only first rows satisfy the explicit braid reduction hypotheses.
Actual Boolean values, quadratic coefficients and positive-gap chamber
identities are derived here; none is assumed as a model characterization.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open BigOperators MaxCaterpillar.Frontier.StarCertificate
variable {h₁ h₂ : ℕ}

noncomputable def rowPairs (net : NormalizedNetwork 5 h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hsupport : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card≤2) :
    ∀ j, BraidPair (net.A j) :=
  fun j => Classical.choice (exists_braidPair (net.A j) (hnorm.1 j) (hsupport j))

noncomputable def innerSetFunction (net : NormalizedNetwork 5 h₁ h₂)
    (k : Fin h₂) (B : Finset (Fin 5)) : ℝ := net.inner k (booleanPoint B)

noncomputable def outputRemainder (net : NormalizedNetwork 5 h₁ h₂) (x : Point 5) : ℝ :=
  lin net.L x+∑ j, net.B j*relu (lin (net.A j) x)

noncomputable def outputSetFunction (net : NormalizedNetwork 5 h₁ h₂)
    (B : Finset (Fin 5)) : ℝ := outputRemainder net (booleanPoint B)

noncomputable def innerLinear (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂) : Point 5 :=
  linearCombinationCoeff (net.U k) (net.W k) net.A pairs

noncomputable def innerQuadratic (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂) : Fin 5→Fin 5→ℝ :=
  quadraticCombinationCoeff (net.W k) net.A pairs

noncomputable def outputLinear (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) : Point 5 :=
  linearCombinationCoeff net.L net.B net.A pairs

noncomputable def outputQuadratic (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) : Fin 5→Fin 5→ℝ :=
  quadraticCombinationCoeff net.B net.A pairs

theorem inner_boolean_quadratic (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂) (B : Finset (Fin 5)) :
    innerSetFunction net k B=
      booleanQuadratic 0 (innerLinear net pairs k) (innerQuadratic net pairs k) B :=
  braid_linear_combination_boolean (net.U k) (net.W k) net.A pairs B

theorem output_boolean_quadratic (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (B : Finset (Fin 5)) :
    outputSetFunction net B=
      booleanQuadratic 0 (outputLinear net pairs) (outputQuadratic net pairs) B :=
  braid_linear_combination_boolean net.L net.B net.A pairs B

@[simp] theorem booleanPoint_empty : booleanPoint ∅=(0 : Point 5) := by
  funext i
  simp [booleanPoint,booleanCoordinate]

@[simp] theorem booleanPoint_univ : booleanPoint Finset.univ=diag (1 : ℝ) := by
  funext i
  simp [booleanPoint,booleanCoordinate,diag]

theorem innerSetFunction_empty (net : NormalizedNetwork 5 h₁ h₂) (k : Fin h₂) :
    innerSetFunction net k ∅=0 := by
  rw [innerSetFunction,booleanPoint_empty,NormalizedNetwork.inner_zero]

theorem innerSetFunction_full (net : NormalizedNetwork 5 h₁ h₂)
    (hnorm : net.TranslationNormalized) (k : Fin h₂) :
    innerSetFunction net k Finset.univ=0 := by
  simp only [innerSetFunction,booleanPoint_univ,NormalizedNetwork.inner,lin_diag,one_mul,
    hnorm.1,hnorm.2.1,relu_of_nonneg (le_refl (0 : ℝ)),mul_zero,
    Finset.sum_const_zero,add_zero]

theorem innerSetFunction_mobius_zero (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂) :
    topMobius (innerSetFunction net k)=0 := by
  have he : innerSetFunction net k=
      booleanQuadratic 0 (innerLinear net pairs k) (innerQuadratic net pairs k) :=
    funext (inner_boolean_quadratic net pairs k)
  rw [he]
  exact topMobius_booleanQuadratic _ _ _

theorem inner_interaction_support (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂) (i l : Fin 5)
    (h : effectiveInteraction (innerQuadratic net pairs k) i l≠0) :
    ∃ j, net.W k j≠0 ∧ net.A j i≠0 ∧ net.A j l≠0 :=
  quadraticCombination_symm_nonzero_support (net.W k) net.A pairs i l h

theorem first_relu_chamber (a : Point 5) (pair : BraidPair a)
    (p : Fin 120) (d : Point 4) (hd : ∀ r, 0≤d r) :
    relu (lin a (chamberPoint p d))=
      ∑ r : Fin 4, d r*relu (lin a (booleanPoint (chamberPrefix p r))) := by
  simp_rw [pair.lin_eq]
  exact relu_pair_chamber p d hd pair.left pair.right pair.scale

theorem braid_linear_combination_chamber {ι : Type*} [Fintype ι]
    (U : Point 5) (c : ι→ℝ) (A : ι→Point 5) (pairs : ∀ j, BraidPair (A j))
    (p : Fin 120) (d : Point 4) (hd : ∀ r, 0≤d r) :
    lin U (chamberPoint p d)+(∑ j, c j*relu (lin (A j) (chamberPoint p d)))=
      ∑ r : Fin 4, d r*(lin U (booleanPoint (chamberPrefix p r))+
        ∑ j, c j*relu (lin (A j) (booleanPoint (chamberPrefix p r)))) := by
  have hf := chamber_linear_combination (fun j x => relu (lin (A j) x)) c p d
    (fun j => first_relu_chamber (A j) (pairs j) p d hd)
  rw [lin_chamberPoint,hf,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Actual unrectified outer preactivations are their Boolean-prefix linear
forms throughout every closed positive-gap chamber. -/
theorem inner_chamber (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (k : Fin h₂)
    (p : Fin 120) (d : Point 4) (hd : ∀ r, 0≤d r) :
    net.inner k (chamberPoint p d)=lin (setFunctionChain (innerSetFunction net k) p) d := by
  change lin (net.U k) (chamberPoint p d)+
    (∑ j, net.W k j*relu (lin (net.A j) (chamberPoint p d)))=_
  rw [braid_linear_combination_chamber (net.U k) (net.W k) net.A pairs p d hd]
  change (∑ r : Fin 4, d r*(net.inner k (booleanPoint (chamberPrefix p r))))=
    ∑ r : Fin 4, net.inner k (booleanPoint (chamberPrefix p r))*d r
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem outputRemainder_chamber (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j))
    (p : Fin 120) (d : Point 4) (hd : ∀ r, 0≤d r) :
    outputRemainder net (chamberPoint p d)=
      lin (setFunctionChain (outputSetFunction net) p) d := by
  rw [outputRemainder,
    braid_linear_combination_chamber net.L net.B net.A pairs p d hd]
  change (∑ r : Fin 4, d r*(outputRemainder net (booleanPoint (chamberPrefix p r))))=
    ∑ r : Fin 4, outputRemainder net (booleanPoint (chamberPrefix p r))*d r
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The exact positive-gap affine identities required by the Möbius theorem
follow from an actual all-input Max5 network equality. -/
theorem actual_chamber_identity (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j))
    (hnet : ∀ x, net.eval x=Maximum 5 x) :
    ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ r, 0<x r) →
        lin l x+β=∑ k, net.d k*relu (lin (setFunctionChain (innerSetFunction net k) p) x) := by
  intro p
  refine ⟨(fun r => 1-outputSetFunction net (chamberPrefix p r)),0,?_⟩
  intro x hx
  have hd : ∀ r, 0≤x r := fun r => (hx r).le
  have he := hnet (chamberPoint p x)
  change outputRemainder net (chamberPoint p x)+
    (∑ k, net.d k*relu (net.inner k (chamberPoint p x)))=Maximum 5 (chamberPoint p x) at he
  rw [outputRemainder_chamber net pairs p x hd,maximum_chamberPoint p x hd] at he
  simp_rw [inner_chamber net pairs _ p x hd] at he
  change (∑ r : Fin 4, outputSetFunction net (chamberPrefix p r)*x r)+
    (∑ k, net.d k*relu (lin (setFunctionChain (innerSetFunction net k) p) x))=
      ∑ r : Fin 4, x r at he
  have hl : lin (fun r => 1-outputSetFunction net (chamberPrefix p r)) x+0=
      (∑ r : Fin 4, x r)-(∑ r : Fin 4, outputSetFunction net (chamberPrefix p r)*x r) := by
    simp only [lin,sub_mul,one_mul,Finset.sum_sub_distrib,add_zero]
  rw [hl]
  linarith only [he]

theorem actual_vertex_decomposition (net : NormalizedNetwork 5 h₁ h₂)
    (pairs : ∀ j, BraidPair (net.A j)) (B : Finset (Fin 5)) :
    net.eval (fun i => booleanCoordinate i B)=
      (∑ k, net.d k*relu (innerSetFunction net k B))+
        booleanQuadratic 0 (outputLinear net pairs) (outputQuadratic net pairs) B := by
  change outputSetFunction net B+(∑ k, net.d k*relu (innerSetFunction net k B))=_
  rw [output_boolean_quadratic net pairs B]
  ring

/-- An actual translation-normalized indexed network whose every first row
has support at most two cannot compute Max5 if its actual inner neurons
satisfy the separately supplied Xi certificate. -/
theorem not_exact_maximum_of_certificate (net : NormalizedNetwork 5 h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hsupport : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card≤2)
    (hcertificate : ∀ k, (∑ p : Fin 120,
      starXi (setFunctionChain (innerSetFunction net k) p))=0) :
    ¬ (∀ x, net.eval x=Maximum 5 x) := by
  intro hnet
  let pairs := rowPairs net hnorm hsupport
  have hnot := star_certificate_not_exact_maximum net.eval (innerSetFunction net) net.d
    0 (outputLinear net pairs) (outputQuadratic net pairs)
    (actual_vertex_decomposition net pairs) (innerSetFunction_empty net)
    (innerSetFunction_full net hnorm) (innerSetFunction_mobius_zero net pairs)
    hcertificate (actual_chamber_identity net pairs hnet)
  exact hnot hnet

theorem table_certificate_of_permutation_sum (G : Finset (Fin 5)→ℝ)
    (h : (∑ pi : Equiv.Perm (Fin 5), starXi (permutationFunctionChain G pi))=0) :
    (∑ p : Fin 120, starXi (setFunctionChain G p))=0 := by
  change (∑ p : Fin 120, starXi (permutationFunctionChain G (permutationEquiv p)))=0
  exact (sum_permutationTable (fun pi => starXi (permutationFunctionChain G pi))).trans h

theorem not_exact_maximum_of_permutation_certificate (net : NormalizedNetwork 5 h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hsupport : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card≤2)
    (hcertificate : ∀ k, (∑ pi : Equiv.Perm (Fin 5),
      starXi (permutationFunctionChain (innerSetFunction net k) pi))=0) :
    ¬ (∀ x, net.eval x=Maximum 5 x) :=
  not_exact_maximum_of_certificate net hnorm hsupport
    (fun k => table_certificate_of_permutation_sum _ (hcertificate k))

#print axioms inner_boolean_quadratic
#print axioms innerSetFunction_full
#print axioms inner_chamber
#print axioms actual_chamber_identity
#print axioms actual_vertex_decomposition
#print axioms not_exact_maximum_of_certificate
#print axioms not_exact_maximum_of_permutation_certificate
end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
