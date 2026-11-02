import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass.Coordinates

/-! # Actual star chart core equations and complete branch tests

The proofs use the original four incoming coefficients of every core. They
hold throughout both real parameter domains, including every closed endpoint.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star65 Star.PhysicalChart MaxCaterpillar.Frontier

lemma chartI_carrierClass (bits : Fin 3 → Bool) (q : ChartI bits) (b kind : Bool) :
    chartI bits q ∈ carrierClass (Equiv.refl (Fin 5),b,bits,kind) := by
  let r := q.val.1.val.1
  have hr : r ≠ 0 := ne_of_gt q.val.1.property.1
  have h00 : coeff (chartI bits q) 0 0=orientation (chartFlipBits bits 0)*((r-1)/r) :=
    chartI_core_coefficient bits q 0 0
  have h02 : coeff (chartI bits q) 0 2=orientation (chartFlipBits bits 0)*(-1) :=
    chartI_core_coefficient bits q 0 2
  have h03 : coeff (chartI bits q) 0 3=orientation (chartFlipBits bits 0)*(1/r) :=
    chartI_core_coefficient bits q 0 3
  have h13 : coeff (chartI bits q) 1 3=orientation (chartFlipBits bits 1)*0 :=
    chartI_core_coefficient bits q 1 3
  have h11 : coeff (chartI bits q) 1 1=orientation (chartFlipBits bits 1)*1 :=
    chartI_core_coefficient bits q 1 1
  have h12 : coeff (chartI bits q) 1 2=orientation (chartFlipBits bits 1)*(-1) :=
    chartI_core_coefficient bits q 1 2
  change coeff (chartI bits q) 0 0+coeff (chartI bits q) 0 2+
      coeff (chartI bits q) 0 3=0 ∧
    coeff (chartI bits q) 0 2+r*coeff (chartI bits q) 0 3=0 ∧
    coeff (chartI bits q) 1 3=0 ∧
    coeff (chartI bits q) 1 1+coeff (chartI bits q) 1 2=0
  rw [h00,h02,h03,h13,h11,h12]
  refine ⟨?_,?_,?_,?_⟩
  · field_simp [hr] <;> ring
  · field_simp [hr] <;> ring
  · ring
  · ring

lemma chartII_carrierClass (bits : Fin 3 → Bool) (q : ChartII bits) (b kind : Bool) :
    chartII bits q ∈ carrierClass (Equiv.refl (Fin 5),b,bits,kind) := by
  let r := q.val.1.val.1
  have hr : r ≠ 0 := ne_of_gt q.val.1.property.1
  have h00 : coeff (chartII bits q) 0 0=orientation (chartFlipBits bits 0)*((r-1)/r) :=
    chartII_core_coefficient bits q 0 0
  have h02 : coeff (chartII bits q) 0 2=orientation (chartFlipBits bits 0)*(-1) :=
    chartII_core_coefficient bits q 0 2
  have h03 : coeff (chartII bits q) 0 3=orientation (chartFlipBits bits 0)*(1/r) :=
    chartII_core_coefficient bits q 0 3
  have h13 : coeff (chartII bits q) 1 3=orientation (chartFlipBits bits 1)*0 :=
    chartII_core_coefficient bits q 1 3
  have h11 : coeff (chartII bits q) 1 1=orientation (chartFlipBits bits 1)*1 :=
    chartII_core_coefficient bits q 1 1
  have h12 : coeff (chartII bits q) 1 2=orientation (chartFlipBits bits 1)*(-1) :=
    chartII_core_coefficient bits q 1 2
  change coeff (chartII bits q) 0 0+coeff (chartII bits q) 0 2+
      coeff (chartII bits q) 0 3=0 ∧
    coeff (chartII bits q) 0 2+r*coeff (chartII bits q) 0 3=0 ∧
    coeff (chartII bits q) 1 3=0 ∧
    coeff (chartII bits q) 1 1+coeff (chartII bits q) 1 2=0
  rw [h00,h02,h03,h13,h11,h12]
  refine ⟨?_,?_,?_,?_⟩
  · field_simp [hr] <;> ring
  · field_simp [hr] <;> ring
  · ring
  · ring

lemma chartI_branchClass (bits : Fin 3 → Bool) (q : ChartI bits) (kind : Bool) :
    chartI bits q ∈ branchClass (Equiv.refl (Fin 5),false,bits,kind) := by
  let l : Label := (Equiv.refl (Fin 5),false,bits,kind)
  let r := q.val.1.val.1
  let k := q.val.1.val.2
  have hr : r ≠ 0 := ne_of_gt q.val.1.property.1
  have hh : hValue l (chartI bits q)=0 := normalizedCoeff_chartI bits q false kind 0 1
  have hk : kValue l (chartI bits q)=k := normalizedCoeff_chartI bits q false kind 1 0
  have hn0 : normalizedCoeff l (chartI bits q) 2 0=k-1/r :=
    normalizedCoeff_chartI bits q false kind 2 0
  have hn3 : normalizedCoeff l (chartI bits q) 2 3=1/r :=
    normalizedCoeff_chartI bits q false kind 2 3
  have hn : nValue l (chartI bits q)=k-1 := by
    change normalizedCoeff l (chartI bits q) 2 0+(1-r)*
      normalizedCoeff l (chartI bits q) 2 3=k-1
    rw [hn0,hn3]
    field_simp [hr] <;> ring
  have hm : mValue l (chartI bits q)=0 := normalizedCoeff_chartI bits q false kind 2 1
  have hl : lValue l (chartI bits q)=1 := by
    change r*normalizedCoeff l (chartI bits q) 2 3=1
    rw [hn3]
    field_simp [hr]
  change hValue l (chartI bits q)=0 ∧ kValue l (chartI bits q)≤0 ∧
    nValue l (chartI bits q)=kValue l (chartI bits q)-1 ∧
    mValue l (chartI bits q)=0 ∧ lValue l (chartI bits q)=1
  rw [hh,hk,hn,hm,hl]
  exact ⟨rfl,q.val.1.property.2.2,rfl,rfl,rfl⟩

lemma chartII_branchClass (bits : Fin 3 → Bool) (q : ChartII bits) (kind : Bool) :
    chartII bits q ∈ branchClass (Equiv.refl (Fin 5),true,bits,kind) := by
  let l : Label := (Equiv.refl (Fin 5),true,bits,kind)
  let r := q.val.1.val.1
  let h := q.val.1.val.2
  have hh : hValue l (chartII bits q)=h := normalizedCoeff_chartII bits q true kind 0 1
  have hk : kValue l (chartII bits q)=1 := normalizedCoeff_chartII bits q true kind 1 0
  have hn0 : normalizedCoeff l (chartII bits q) 2 0=1 :=
    normalizedCoeff_chartII bits q true kind 2 0
  have hn3 : normalizedCoeff l (chartII bits q) 2 3=0 :=
    normalizedCoeff_chartII bits q true kind 2 3
  have hn : nValue l (chartII bits q)=1 := by
    change normalizedCoeff l (chartII bits q) 2 0+(1-r)*
      normalizedCoeff l (chartII bits q) 2 3=1
    rw [hn0,hn3]
    ring
  have hm : mValue l (chartII bits q)=1+h := normalizedCoeff_chartII bits q true kind 2 1
  have hl : lValue l (chartII bits q)=0 := by
    change r*normalizedCoeff l (chartII bits q) 2 3=0
    rw [hn3]
    ring
  change kValue l (chartII bits q)=1 ∧ hValue l (chartII bits q)≤-1 ∧
    nValue l (chartII bits q)=1 ∧ mValue l (chartII bits q)=1+hValue l (chartII bits q) ∧
    lValue l (chartII bits q)=0
  rw [hh,hk,hn,hm,hl]
  exact ⟨rfl,q.val.1.property.2.2,rfl,rfl,rfl⟩

#print axioms chartI_carrierClass
#print axioms chartII_carrierClass
#print axioms chartI_branchClass
#print axioms chartII_branchClass
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
