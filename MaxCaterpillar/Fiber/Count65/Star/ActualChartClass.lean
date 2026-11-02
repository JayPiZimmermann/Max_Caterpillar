import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass.CoreClasses

/-! # The exact actual finite labels of both complete star physical charts

The physical label records a negative W coefficient, so chartFlipBits is the
explicit opposite convention used by the preexisting physical chart.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 Star.PhysicalChart MaxCaterpillar.Frontier

/-- Every point of the complete first chart has its original-coefficient
finite physical class, including the r=1 and slack=0 endpoints. -/
theorem chartI_mem_physicalClass (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartI bits) (hq : q ∈ headSectorI bits kind) :
    chartI bits q ∈ physicalClass (Equiv.refl (Fin 5),false,bits,kind) := by
  have ho : chartI bits q ∈ outputClass (Equiv.refl (Fin 5),false,bits,kind) := by
    intro i
    fin_cases i <;> rfl
  have hs : chartI bits q ∈ stationaryClass (Equiv.refl (Fin 5),false,bits,kind) := by
    intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  have hw : chartI bits q ∈ orientationClass (Equiv.refl (Fin 5),false,bits,kind) := by
    intro i
    change (branchIChart (chartFlipBits bits) q).W₂ (Fin.castAdd 2 i) 2=eps bits i
    rw [branchIChart_core_W,orientation_chartFlipBits]
    ring
  have hd : chartI bits q ∈ directionClass (Equiv.refl (Fin 5),false,bits,kind) :=
    ⟨chartI_carrierClass bits q false kind,chartI_branchClass bits q kind⟩
  have ht := (headSectorI_iff_test bits kind q).mp hq
  have hh : chartI bits q ∈ headClass (Equiv.refl (Fin 5),false,bits,kind) := by
    cases kind
    · change ∀ x : InvariantState,0 ≤ intercept (chartI bits q) 3 x ∧
        0 ≤ intercept (chartI bits q) 4 x
      intro x
      rw [chartI_intercept_positive,chartI_intercept_negative]
      exact ht _
    · change ∀ x : InvariantState,intercept (chartI bits q) 3 x+
        intercept (chartI bits q) 4 x=0
      intro x
      rw [chartI_intercept_positive,chartI_intercept_negative]
      exact ht _
  exact ⟨⟨⟨⟨ho,hs⟩,hw⟩,hd⟩,hh⟩

/-- The complete second chart has the same exact labeling, including its
closed slack=-1 and dictionary r=1 endpoints. -/
theorem chartII_mem_physicalClass (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartII bits) (hq : q ∈ headSectorII bits kind) :
    chartII bits q ∈ physicalClass (Equiv.refl (Fin 5),true,bits,kind) := by
  have ho : chartII bits q ∈ outputClass (Equiv.refl (Fin 5),true,bits,kind) := by
    intro i
    fin_cases i <;> rfl
  have hs : chartII bits q ∈ stationaryClass (Equiv.refl (Fin 5),true,bits,kind) := by
    intro i
    fin_cases i <;> exact ⟨rfl,rfl⟩
  have hw : chartII bits q ∈ orientationClass (Equiv.refl (Fin 5),true,bits,kind) := by
    intro i
    change (branchIIChart (chartFlipBits bits) q).W₂ (Fin.castAdd 2 i) 2=eps bits i
    rw [branchIIChart_core_W,orientation_chartFlipBits]
    ring
  have hd : chartII bits q ∈ directionClass (Equiv.refl (Fin 5),true,bits,kind) :=
    ⟨chartII_carrierClass bits q true kind,chartII_branchClass bits q kind⟩
  have ht := (headSectorII_iff_test bits kind q).mp hq
  have hh : chartII bits q ∈ headClass (Equiv.refl (Fin 5),true,bits,kind) := by
    cases kind
    · change ∀ x : InvariantState,0 ≤ intercept (chartII bits q) 3 x ∧
        0 ≤ intercept (chartII bits q) 4 x
      intro x
      rw [chartII_intercept_positive,chartII_intercept_negative]
      exact ht _
    · change ∀ x : InvariantState,intercept (chartII bits q) 3 x+
        intercept (chartII bits q) 4 x=0
      intro x
      rw [chartII_intercept_positive,chartII_intercept_negative]
      exact ht _
  exact ⟨⟨⟨⟨ho,hs⟩,hw⟩,hd⟩,hh⟩

lemma actualLabel_chartI (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartI bits) (hq : q ∈ headSectorI bits kind) :
    actualLabel (chartI bits q)=(Equiv.refl (Fin 5),false,bits,kind) :=
  (actualLabel_eq_iff _ _).mpr (chartI_mem_physicalClass bits kind q hq)
lemma actualLabel_chartII (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartII bits) (hq : q ∈ headSectorII bits kind) :
    actualLabel (chartII bits q)=(Equiv.refl (Fin 5),true,bits,kind) :=
  (actualLabel_eq_iff _ _).mpr (chartII_mem_physicalClass bits kind q hq)
lemma componentLabel_chartI (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartI bits) (hq : q ∈ headSectorI bits kind) : componentLabel (chartI bits q)=(false,bits,kind) := by
  unfold componentLabel
  rw [actualLabel_chartI bits kind q hq]
lemma componentLabel_chartII (bits : Fin 3 → Bool) (kind : Bool)
    (q : ChartII bits) (hq : q ∈ headSectorII bits kind) : componentLabel (chartII bits q)=(true,bits,kind) := by
  unfold componentLabel
  rw [actualLabel_chartII bits kind q hq]

lemma headSectorI_exhaustive (bits : Fin 3 → Bool) (q : ChartI bits) :
    ∃ kind : Bool,q ∈ headSectorI bits kind := by
  classical
  by_cases hs : (HeadTopology.toHeads q.val.2).IsSigned (remainderI bits q.val.1 : InvariantState → ℝ)
  · exact ⟨true,hs⟩
  · exact ⟨false,hs⟩
lemma headSectorII_exhaustive (bits : Fin 3 → Bool) (q : ChartII bits) :
    ∃ kind : Bool,q ∈ headSectorII bits kind := by
  classical
  by_cases hs : (HeadTopology.toHeads q.val.2).IsSigned (remainderII bits q.val.1 : InvariantState → ℝ)
  · exact ⟨true,hs⟩
  · exact ⟨false,hs⟩

#print axioms chartI_mem_physicalClass
#print axioms chartII_mem_physicalClass
#print axioms componentLabel_chartI
#print axioms componentLabel_chartII
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
