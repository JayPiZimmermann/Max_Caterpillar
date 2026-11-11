import MaxCaterpillar.Fiber.BiasQuotient
import MaxCaterpillar.Fiber.Symmetry

/-! # Actual exact-network paths project to the genuine quotients

Bias removal continuously sends any exhibited full-fiber quotient path to the
zero-bias quotient. Thus component assembly does not assume path lifting in a
quotient or infer fixed-first paths from their endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
variable {N h₁ h₂ : ℕ} [NeZero N]

theorem joinedIn_exact_quotient (a b : ExactFiber N h₁ h₂)
    (h : JoinedIn (ExactSet N h₁ h₂) a.val b.val) :
    Joined (quotientMk a) (quotientMk b) := by
  exact ⟨h.joined_subtype.somePath.map quotientMk_continuous⟩

private theorem eraseBiasRespect (a b : ExactFiber N h₁ h₂)
    (h : (symmetrySetoid N h₁ h₂).r a b) :
    (zeroBiasSymmetrySetoid N h₁ h₂).r (zeroBiasRetraction a) (zeroBiasRetraction b) := by
  change (symmetrySetoid N h₁ h₂).r (zeroBiasFiber a) (zeroBiasFiber b)
  exact zeroBiasFiber_symmetry h

noncomputable def eraseBiasQuotient : SymmetryQuotient N h₁ h₂ → ZeroBiasSymmetryQuotient N h₁ h₂ :=
  Quotient.map' zeroBiasRetraction eraseBiasRespect

theorem continuous_eraseBiasQuotient : Continuous (@eraseBiasQuotient N h₁ h₂ _) :=
  continuous_zeroBiasRetraction.quotient_map' eraseBiasRespect

lemma eraseBiasQuotient_zeroPoint (a : ZeroBiasFiber N h₁ h₂) :
    eraseBiasQuotient (quotientMk a.val)=Quotient.mk (zeroBiasSymmetrySetoid N h₁ h₂) a := by
  exact congrArg (Quotient.mk (zeroBiasSymmetrySetoid N h₁ h₂))
    (zeroBiasRetraction_include a)

/-- Transfer a genuine full quotient path with zero-bias endpoints to exactly
the quotient used in component counting, without assuming any lifting. -/
theorem joined_zeroQuotient_of_joined_full (a b : ZeroBiasFiber N h₁ h₂)
    (h : Joined (quotientMk a.val) (quotientMk b.val)) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid N h₁ h₂) a)
      (Quotient.mk (zeroBiasSymmetrySetoid N h₁ h₂) b) := by
  have hp := h.somePath.map continuous_eraseBiasQuotient
  rw [eraseBiasQuotient_zeroPoint,eraseBiasQuotient_zeroPoint] at hp
  exact ⟨hp⟩

theorem joinedIn_exact_zeroQuotient (a b : ZeroBiasFiber N h₁ h₂)
    (h : JoinedIn (ExactSet N h₁ h₂) a.val.val b.val.val) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid N h₁ h₂) a)
      (Quotient.mk (zeroBiasSymmetrySetoid N h₁ h₂) b) :=
  joined_zeroQuotient_of_joined_full a b (joinedIn_exact_quotient a.val b.val h)

end MaxCaterpillar.Fiber.Count65.Paired
