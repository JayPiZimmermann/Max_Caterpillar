import MaxCaterpillar.Fiber.Count65.Paired.Absorption
import MaxCaterpillar.Fiber.ScalingPaths

/-! Positive second-hidden-layer normalization in actual parameter space. -/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.PairNormalization

open Absorption BigOperators
variable {N m k : ℕ}

/-- Only the two selected slots are rescaled. -/
noncomputable def pairScales (a : Network N m k) (p n : Fin k) (i : Fin k) : ℝ :=
  if i = p then a.w₃ p else if i = n then -a.w₃ n else 1

lemma pairScales_pos (a : Network N m k) (p n : Fin k)
    (hp : 0 < a.w₃ p) (hn : a.w₃ n < 0) : ∀ i, 0 < pairScales a p n i := by
  intro i
  unfold pairScales
  split_ifs <;> linarith

/-- Normalize opposite output signs to `1` and `-1` by positive rescaling. -/
noncomputable def normalizePair (a : Network N m k) (p n : Fin k) : Network N m k :=
  scaleSecond a (pairScales a p n)

@[simp] lemma normalizePair_W₁ (a : Network N m k) (p n : Fin k) :
    (normalizePair a p n).W₁ = a.W₁ := rfl
@[simp] lemma normalizePair_b₁ (a : Network N m k) (p n : Fin k) :
    (normalizePair a p n).b₁ = a.b₁ := rfl
@[simp] lemma normalizePair_b₃ (a : Network N m k) (p n : Fin k) :
    (normalizePair a p n).b₃ = a.b₃ := rfl

lemma normalizePair_output_pos (a : Network N m k) (p n : Fin k)
    (hp : 0 < a.w₃ p) : (normalizePair a p n).w₃ p = 1 := by
  simp [normalizePair, scaleSecond, pairScales, ne_of_gt hp]

lemma normalizePair_output_neg (a : Network N m k) (p n : Fin k)
    (hpn : p ≠ n) (hn : a.w₃ n < 0) : (normalizePair a p n).w₃ n = -1 := by
  simp [normalizePair, scaleSecond, pairScales, Ne.symm hpn, ne_of_lt hn]

lemma normalizePair_unselected (a : Network N m k) (p n i : Fin k)
    (hip : i ≠ p) (hin : i ≠ n) :
    (normalizePair a p n).W₂ i = a.W₂ i ∧
    (normalizePair a p n).b₂ i = a.b₂ i ∧
    (normalizePair a p n).w₃ i = a.w₃ i := by
  simp [normalizePair, scaleSecond, pairScales, hip, hin]

lemma scaleSecond_preact (a : Network N m k) (s : Fin k → ℝ)
    (i : Fin k) (x : Point N) :
    preact (scaleSecond a s).W₁ (scaleSecond a s).b₁
      ((scaleSecond a s).W₂ i) ((scaleSecond a s).b₂ i) x =
      s i * preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x :=
  preact_smul a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) (s i) x

lemma scaleSecond_weighted_preact (a : Network N m k) (s : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (i : Fin k) (x : Point N) :
    (scaleSecond a s).w₃ i * relu
      (preact (scaleSecond a s).W₁ (scaleSecond a s).b₁
        ((scaleSecond a s).W₂ i) ((scaleSecond a s).b₂ i) x) =
    a.w₃ i * relu (preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x) := by
  rw [scaleSecond_preact, Frontier.relu_mul_pos (hs i)]
  change (a.w₃ i / s i) * (s i * _) = _
  field_simp [ne_of_gt (hs i)]
  ring

theorem normalizePair_sum_preserved (a : Network N m k) (p n : Fin k)
    (hp : 0 < a.w₃ p) (hn : a.w₃ n < 0) (S : Finset (Fin k)) (x : Point N) :
    (∑ i in S, (normalizePair a p n).w₃ i * relu
      (preact (normalizePair a p n).W₁ (normalizePair a p n).b₁
        ((normalizePair a p n).W₂ i) ((normalizePair a p n).b₂ i) x)) =
    ∑ i in S, a.w₃ i * relu (preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x) := by
  apply Finset.sum_congr rfl
  intro i _
  exact scaleSecond_weighted_preact a _ (pairScales_pos a p n hp hn) i x

/-- Functional weighted cancellation suffices; the raw rows need not agree. -/
theorem normalizePair_preact_opposite (a : Network N m k) (p n : Fin k)
    (hpn : p ≠ n)
    (hcancel : ∀ x, a.w₃ p * preact a.W₁ a.b₁ (a.W₂ p) (a.b₂ p) x =
      a.w₃ n * preact a.W₁ a.b₁ (a.W₂ n) (a.b₂ n) x) (x : Point N) :
    preact (normalizePair a p n).W₁ (normalizePair a p n).b₁
      ((normalizePair a p n).W₂ n) ((normalizePair a p n).b₂ n) x =
    -preact (normalizePair a p n).W₁ (normalizePair a p n).b₁
      ((normalizePair a p n).W₂ p) ((normalizePair a p n).b₂ p) x := by
  simp only [normalizePair, scaleSecond_preact]
  simpa [pairScales, Ne.symm hpn] using congrArg Neg.neg (hcancel x).symm

theorem normalizePair_eval (a : Network N m k) (p n : Fin k)
    (hp : 0 < a.w₃ p) (hn : a.w₃ n < 0) (x : Point N) :
    (normalizePair a p n).eval x = a.eval x :=
  scaleSecond_eval a _ (pairScales_pos a p n hp hn) x

variable [NeZero N]

noncomputable def normalizePairFiber (a : ExactFiber N m k) (p n : Fin k)
    (hp : 0 < a.val.w₃ p) (hn : a.val.w₃ n < 0) : ExactFiber N m k :=
  scaleSecondFiber (pairScales a.val p n) (pairScales_pos a.val p n hp hn) a

noncomputable def normalizePairPath (a : ExactFiber N m k) (p n : Fin k)
    (hp : 0 < a.val.w₃ p) (hn : a.val.w₃ n < 0) :
    Path a (normalizePairFiber a p n hp hn) :=
  scaleSecondPath _ (pairScales_pos a.val p n hp hn) a

lemma normalizePairPath_fixed (a : ExactFiber N m k) (p n : Fin k)
    (hp : 0 < a.val.w₃ p) (hn : a.val.w₃ n < 0) (t : unitInterval) :
    (normalizePairPath a p n hp hn t).val.W₁ = a.val.W₁ ∧
    (normalizePairPath a p n hp hn t).val.b₁ = a.val.b₁ ∧
    (normalizePairPath a p n hp hn t).val.b₃ = a.val.b₃ := ⟨rfl, rfl, rfl⟩

lemma normalizePairPath_unselected (a : ExactFiber N m k) (p n : Fin k)
    (hp : 0 < a.val.w₃ p) (hn : a.val.w₃ n < 0) (t : unitInterval)
    (i : Fin k) (hip : i ≠ p) (hin : i ≠ n) :
    (normalizePairPath a p n hp hn t).val.W₂ i = a.val.W₂ i ∧
    (normalizePairPath a p n hp hn t).val.b₂ i = a.val.b₂ i ∧
    (normalizePairPath a p n hp hn t).val.w₃ i = a.val.w₃ i := by
  change (fun j => scaleSegment (pairScales a.val p n) t i * a.val.W₂ i j) = a.val.W₂ i ∧
    scaleSegment (pairScales a.val p n) t i * a.val.b₂ i = a.val.b₂ i ∧
    a.val.w₃ i / scaleSegment (pairScales a.val p n) t i = a.val.w₃ i
  have hs : scaleSegment (pairScales a.val p n) t i = 1 := by
    simp [scaleSegment, pairScales, hip, hin]
  simp [hs]

theorem normalizePair_joinedIn_exact (a : ExactFiber N m k) (p n : Fin k)
    (hp : 0 < a.val.w₃ p) (hn : a.val.w₃ n < 0) :
    JoinedIn (ExactSet N m k) a.val (normalizePair a.val p n) := by
  exact ⟨(normalizePairPath a p n hp hn).map continuous_subtype_val,
    fun t => (normalizePairPath a p n hp hn t).property⟩

end MaxCaterpillar.Fiber.Count65.Paired.PairNormalization
