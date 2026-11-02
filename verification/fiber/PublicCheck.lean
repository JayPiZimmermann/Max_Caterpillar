import MaxCaterpillar

set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Fiber

example : ∀ {h₁ h₂ : ℕ},
    Nonempty (SymmetryQuotient 4 h₁ h₂) ↔ 6 ≤ h₁ ∧ 3 ≤ h₂ :=
  @max4_symmetryQuotient_nonempty_iff

example : ∀ {N h₁ h₂ : ℕ} [NeZero N] (count : ℕ),
    HasComponentCount N h₁ h₂ count ↔
      Nonempty (ConnectedComponents (ZeroBiasSymmetryQuotient N h₁ h₂) ≃ Fin count) :=
  @hasComponentCount_iff_zeroBias

example : ∀ {N h₁ h₂ : ℕ} [NeZero N],
    ConnectedComponents (SymmetryQuotient N h₁ h₂) ≃
      ConnectedComponents (ZeroBiasSymmetryQuotient N h₁ h₂) :=
  @zeroBiasQuotientConnectedComponentsEquiv

example : ∀ {N h₁ h₂ : ℕ} [NeZero N], IsClosed (ExactSet N h₁ h₂) :=
  @isClosed_exactSet

#print axioms max4_symmetryQuotient_nonempty_iff
#print axioms hasComponentCount_iff_zeroBias
#print axioms zeroBiasQuotientConnectedComponentsEquiv
#print axioms isClosed_exactSet
