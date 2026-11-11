import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Physical incoming-row interpolation from equality on natural features

All first parameters and output parameters remain fixed. A second incoming
row may be replaced by any other row inducing the same preactivation on all
real inputs. Dormant output slots may be replaced freely. This is a continuous
path of actual parameters; no internal code change is identified with a path.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators
variable {N m r : ℕ}

noncomputable def withSecondRows (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ) : Network N m r :=
  {net with W₂ := A, b₂ := b}

noncomputable def interpolateSecondRows (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ) (t : ℝ) : Network N m r :=
  withSecondRows net ((1-t) • net.W₂+t • A) ((1-t) • net.b₂+t • b)

lemma interpolateSecondRows_preact (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ) (t : ℝ) (k : Fin r)
    (x : Point N) :
    Absorption.preact net.W₁ net.b₁ (((1-t) • net.W₂+t • A) k)
        (((1-t) • net.b₂+t • b) k) x =
      (1-t)*Absorption.preact net.W₁ net.b₁ (net.W₂ k) (net.b₂ k) x+
        t*Absorption.preact net.W₁ net.b₁ (A k) (b k) x := by
  simp only [Absorption.preact,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

/-- Functionally equal active incoming rows may be linearly interpolated;
zero-output rows may be repurposed without any condition on their features. -/
theorem interpolateSecondRows_eval (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ)
    (h : ∀ k, net.w₃ k≠0 → ∀ x,
      Absorption.preact net.W₁ net.b₁ (A k) (b k) x=
        Absorption.preact net.W₁ net.b₁ (net.W₂ k) (net.b₂ k) x)
    (t : ℝ) (x : Point N) :
    (interpolateSecondRows net A b t).eval x=net.eval x := by
  change (∑ k, net.w₃ k*relu (Absorption.preact net.W₁ net.b₁
      (((1-t) • net.W₂+t • A) k) (((1-t) • net.b₂+t • b) k) x))+net.b₃ =
    (∑ k, net.w₃ k*relu (Absorption.preact net.W₁ net.b₁ (net.W₂ k) (net.b₂ k) x))+net.b₃
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : net.w₃ k=0
  · simp only [hk,zero_mul]
  · rw [interpolateSecondRows_preact,h k hk x]
    congr 2
    ring

lemma interpolateSecondRows_zero (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ) :
    interpolateSecondRows net A b 0=net := by
  simp [interpolateSecondRows,withSecondRows]

lemma interpolateSecondRows_one (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ) :
    interpolateSecondRows net A b 1=withSecondRows net A b := by
  simp [interpolateSecondRows]

theorem continuous_interpolateSecondRows (net : Network N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ) :
    Continuous (interpolateSecondRows net A b) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    simp only [interpolateSecondRows,withSecondRows,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    continuity
  · apply continuous_pi
    intro k
    simp only [interpolateSecondRows,withSecondRows,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    continuity

/-- The equality on natural preactivations is realized by an actual exact-fiber
path with arbitrary biases and arbitrary unused spectator slots. -/
noncomputable def rowInterpolationPath [NeZero N] (net : ExactFiber N m r)
    (A : Fin r → Fin m → ℝ) (b : Fin r → ℝ)
    (h : ∀ k, net.val.w₃ k≠0 → ∀ x,
      Absorption.preact net.val.W₁ net.val.b₁ (A k) (b k) x=
        Absorption.preact net.val.W₁ net.val.b₁ (net.val.W₂ k) (net.val.b₂ k) x) :
    Path net (⟨withSecondRows net.val A b, fun x => by
      have hh := interpolateSecondRows_eval net.val A b h 1 x
      rw [interpolateSecondRows_one] at hh
      exact hh.trans (net.property x)⟩ : ExactFiber N m r) where
  toFun t := ⟨interpolateSecondRows net.val A b t,
    fun x => (interpolateSecondRows_eval net.val A b h t x).trans (net.property x)⟩
  continuous_toFun := ((continuous_interpolateSecondRows net.val A b).comp
    continuous_subtype_val).subtype_mk _
  source' := by apply Subtype.ext; exact interpolateSecondRows_zero net.val A b
  target' := by apply Subtype.ext; exact interpolateSecondRows_one net.val A b

end MaxCaterpillar.Fiber.Count65.Paired
