import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.Canonical

/-! Functional natural-row matching is realized by a physical row path. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
open Absorption

theorem comparator_source_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (e : Equiv.Perm (Fin 5)) (s : ℝ)
    (hreadout : ∀ i, a.val.w₃ (e i) = (comparatorNet U s 0).w₃ i)
    (hnatural : ∀ i, a.val.w₃ (e i) ≠ 0 → ∀ x,
      endpointForm U (a.val.W₂ (e i)) x =
        endpointForm U ((comparatorNet U s 0).W₂ i) x) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  let r := reindexSecondFiber e a
  let t := comparatorPoint U hdet s 0
  have htb : t.val.b₂ = 0 := by
    funext i
    fin_cases i
    · change (0 : ℝ)=0
      rfl
    · change -(0 : ℝ)=0
      ring
    · change (0 : ℝ)+s*0=0
      ring
    · change -((0 : ℝ)+s*0)=0
      ring
    · change (0 : ℝ)=0
      rfl
  have hrow : ∀ i, r.val.w₃ i ≠ 0 → ∀ x,
      preact r.val.W₁ r.val.b₁ (t.val.W₂ i) (t.val.b₂ i) x =
        preact r.val.W₁ r.val.b₁ (r.val.W₂ i) (r.val.b₂ i) x := by
    intro i hi x
    change preact a.val.W₁ a.val.b₁ (t.val.W₂ i) (t.val.b₂ i) x =
      preact a.val.W₁ a.val.b₁ (a.val.W₂ (e i)) (a.val.b₂ (e i)) x
    rw [hU,hb.1,hb.2.1,htb]
    simp only [Pi.zero_apply,preact_pairedRows_zero]
    exact (hnatural i hi x).symm
  have heq : withSecondRows r.val t.val.W₂ t.val.b₂ = t.val := by
    apply (networkEquivParameters 4 6 5).injective
    refine Prod.ext hU (Prod.ext hb.1 (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ hb.2.2))))
    funext i
    exact hreadout i
  let b : ExactFiber 4 6 5 := ⟨withSecondRows r.val t.val.W₂ t.val.b₂,
    fun x => by rw [heq]; exact t.property x⟩
  have hbt : b = t := Subtype.ext heq
  have hp : Path r b := rowInterpolationPath r t.val.W₂ t.val.b₂ hrow
  rw [hbt] at hp
  have hj : Joined (quotientMk r) (quotientMk t) :=
    ⟨hp.map quotientMk_continuous⟩
  rw [quotient_reindexSecond a e] at hj
  exact hj.trans (comparator_quotient_joined U hdet s 0)

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
