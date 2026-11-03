import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization

/-! Coordinate identification preserves the actual affine-skip network
function on the identified subspace. Surjectivity preserves the MAX target.
This is a model morphism, not a width bound stronger than generic deletion. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.CoordinateQuotient
open BigOperators Frontier Frontier.RandomRestriction
open AffineSkipExtension
open NormalizedNetwork (rowSupport)
variable {N m h₁ h₂ : ℕ}

def pullback (φ : Fin N → Fin m) (x : Point m) : Point N := fun i => x (φ i)

def blockSum (φ : Fin N → Fin m) (a : Point N) : Point m :=
  fun b => ∑ i, if φ i = b then a i else 0

theorem blockSum_dot (φ : Fin N → Fin m) (a : Point N) (x : Point m) :
    (∑ b, blockSum φ a b * x b) = ∑ i, a i * x (φ i) := by
  classical
  simp only [blockSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  simp

theorem blockSum_sum (φ : Fin N → Fin m) (a : Point N) :
    (∑ b, blockSum φ a b) = ∑ i, a i := by
  classical
  unfold blockSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

def quotient (net : AffineSkipNetwork N h₁ h₂) (φ : Fin N → Fin m) :
    AffineSkipNetwork m h₁ h₂ where
  A j := blockSum φ (net.A j)
  b := net.b
  W := net.W
  U k := blockSum φ (net.U k)
  θ := net.θ
  d := net.d
  B := net.B
  L := blockSum φ net.L
  β := net.β

theorem first_quotient (net : AffineSkipNetwork N h₁ h₂)
    (φ : Fin N → Fin m) (j : Fin h₁) (x : Point m) :
    first (quotient net φ) j x = first net j (pullback φ x) := by
  simp only [first, quotient, blockSum_dot, pullback]

theorem inner_quotient (net : AffineSkipNetwork N h₁ h₂)
    (φ : Fin N → Fin m) (k : Fin h₂) (x : Point m) :
    AffineSkipExtension.inner (quotient net φ) k x =
      AffineSkipExtension.inner net k (pullback φ x) := by
  change (∑ j, net.W k j * first (quotient net φ) j x) +
      (∑ b, blockSum φ (net.U k) b * x b) + net.θ k = _
  simp only [first_quotient, blockSum_dot, AffineSkipExtension.inner, pullback]

theorem eval_quotient (net : AffineSkipNetwork N h₁ h₂)
    (φ : Fin N → Fin m) (x : Point m) :
    eval (quotient net φ) x = eval net (pullback φ x) := by
  change (∑ k, net.d k * relu (AffineSkipExtension.inner (quotient net φ) k x)) +
      ((∑ j, net.B j * first (quotient net φ) j x) +
        (∑ b, blockSum φ net.L b * x b) + net.β) = _
  simp only [inner_quotient, first_quotient, blockSum_dot, eval, outputSkip, pullback]

theorem maximum_pullback [NeZero N] [NeZero m] (φ : Fin N → Fin m)
    (hφ : Function.Surjective φ) (x : Point m) :
    Maximum N (pullback φ x) = Maximum m x := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    exact le_Maximum x (φ i)
  · apply (Maximum_le_iff _ _).mpr
    intro b
    obtain ⟨i, rfl⟩ := hφ b
    exact le_Maximum (pullback φ x) i

/-- All original first and second hidden indices are preserved. -/
theorem quotient_computes_max [NeZero N] [NeZero m]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, eval net x = Maximum N x)
    (φ : Fin N → Fin m) (hφ : Function.Surjective φ) :
    ∀ x, eval (quotient net φ) x = Maximum m x := by
  intro x
  rw [eval_quotient, hnet, maximum_pullback φ hφ]

/-- Only original zero-bias, zero-sum rows can remain nonlinear after the
faithful normalization. Their block sums must be braid covectors. -/
def BraidBlockSums (net : AffineSkipNetwork N h₁ h₂) (φ : Fin N → Fin m) : Prop :=
  ∀ j, net.b j = 0 → (∑ i, net.A j i) = 0 →
    (rowSupport (blockSum φ (net.A j))).card ≤ 2

theorem normalized_quotient_braid (net : AffineSkipNetwork N h₁ h₂)
    (φ : Fin N → Fin m) (hbraid : BraidBlockSums net φ) :
    ∀ j, (rowSupport ((normalizedModel (quotient net φ)).A j)).card ≤ 2 := by
  classical
  intro j
  rw [normalizedModel_first_row]
  change (rowSupport (if net.b j = 0 ∧ (∑ b, blockSum φ (net.A j) b) = 0
    then blockSum φ (net.A j) else 0)).card ≤ 2
  rw [blockSum_sum]
  by_cases hj : net.b j = 0 ∧ (∑ i, net.A j i) = 0
  · rw [if_pos hj]
    exact hbraid j hj.1 hj.2
  · rw [if_neg hj, NormalizedNetwork.rowSupport_zero, Finset.card_empty]
    exact Nat.zero_le 2

/-- Actual normalized braid model obtained from an actual MAX identity.
This theorem assumes neither a bound on h₁ nor an abstract simulation. -/
theorem exists_normalized_braid_quotient [NeZero N] [NeZero m]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, eval net x = Maximum N x)
    (φ : Fin N → Fin m) (hφ : Function.Surjective φ)
    (hbraid : BraidBlockSums net φ) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x, model.eval x = Maximum m x) ∧ model.TranslationNormalized ∧
      (∀ j, (rowSupport (model.A j)).card ≤ 2) := by
  let model := normalizedModel (quotient net φ)
  have hm := quotient_computes_max net hnet φ hφ
  exact ⟨model, normalizedModel_computes_max _ hm,
    normalizedModel_translation_normalized _ hm, normalized_quotient_braid net φ hbraid⟩

#check @eval_quotient
#check @quotient_computes_max
#check @exists_normalized_braid_quotient
#print axioms blockSum_dot
#print axioms eval_quotient
#print axioms quotient_computes_max
#print axioms exists_normalized_braid_quotient
end MaxCaterpillar.Overnight.CoordinateQuotient
