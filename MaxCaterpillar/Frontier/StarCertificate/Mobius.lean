import MaxCaterpillar.Frontier.StarCertificate.StarModel
import Mathlib.Data.Fintype.Powerset

/-! # The actual top Boolean Möbius coefficient on five coordinates

The chain normalization is exact: the displayed integer certificate weight
`(10,-20,20,-10)` is 240 times the usual factorial weight. Finite checks
below concern only the fixed Boolean lattice and the existing permutation
table; every real-function identity is proved by linearity afterwards.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def topMobiusSign (B : Finset (Fin 5)) : ℤ := (-1)^(5-B.card)

noncomputable def topMobius (F : Finset (Fin 5)→ℝ) : ℝ :=
  ∑ B : Finset (Fin 5), (topMobiusSign B : ℝ)*F B

noncomputable def setFunctionChain (F : Finset (Fin 5)→ℝ) (p : Fin 120) : Point 4 :=
  fun r => F (chamberPrefix p r)

def starOmegaInteger : Fin 4→ℤ := ![10,-20,20,-10]

theorem starOmega_real_cast (r : Fin 4) :
    (starOmega r : ℝ)=(starOmegaInteger r : ℝ) := by
  fin_cases r <;> norm_num [starOmega,starOmegaInteger]

def prefixMobiusWeight (B : Finset (Fin 5)) : ℤ :=
  ∑ p : Fin 120, ∑ r : Fin 4,
    if chamberPrefix p r=B then starOmegaInteger r else 0

theorem prefixMobiusWeight_exact : ∀ B : Finset (Fin 5),
    prefixMobiusWeight B =
      if B=∅ ∨ B=Finset.univ then 0 else 240*topMobiusSign B := by decide

theorem topMobius_add (F G : Finset (Fin 5)→ℝ) :
    topMobius (fun B => F B+G B)=topMobius F+topMobius G := by
  simp only [topMobius,mul_add,Finset.sum_add_distrib]

theorem topMobius_mul (a : ℝ) (F : Finset (Fin 5)→ℝ) :
    topMobius (fun B => a*F B)=a*topMobius F := by
  simp only [topMobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem topMobius_sum {ι : Type*} [Fintype ι] (F : ι→Finset (Fin 5)→ℝ) :
    topMobius (fun B => ∑ i, F i B)=∑ i, topMobius (F i) := by
  simp only [topMobius,Finset.mul_sum]
  exact Finset.sum_comm

/-- Incidence counting over the full, already specified chamber table.
Empty/full values are explicit endpoint hypotheses. -/
theorem sum_weighted_setFunctionChain (F : Finset (Fin 5)→ℝ)
    (h0 : F ∅=0) (h1 : F Finset.univ=0) :
    (∑ p : Fin 120, evalForm starOmega (setFunctionChain F p))=240*topMobius F := by
  have hcollect : (∑ p : Fin 120, evalForm starOmega (setFunctionChain F p))=
      ∑ B : Finset (Fin 5), (prefixMobiusWeight B : ℝ)*F B := by
    unfold evalForm setFunctionChain prefixMobiusWeight
    simp only [starOmega_real_cast,Int.cast_sum,Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    simp only [apply_ite,Int.cast_zero]
    simp [eq_comm]
  rw [hcollect,topMobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [prefixMobiusWeight_exact]
  by_cases hB : B=∅ ∨ B=Finset.univ
  · rcases hB with he | he
    · subst B
      simp [h0]
    · subst B
      simp [h1]
  · simp only [if_neg hB,Int.cast_mul,Int.cast_ofNat]
    ring

theorem twice_relu_eq_add_abs (a : ℝ) : 2*relu a=a+|a| := by
  by_cases ha : 0≤a
  · rw [relu_of_nonneg ha,abs_of_nonneg ha]
    ring
  · rw [relu_of_nonpos (le_of_not_ge ha),abs_of_neg (lt_of_not_ge ha)]
    ring

theorem twice_topMobius_relu (F : Finset (Fin 5)→ℝ) :
    2*topMobius (fun B => relu (F B))=
      topMobius F+topMobius (fun B => |F B|) := by
  rw [←topMobius_mul,←topMobius_add]
  congr 1
  funext B
  exact twice_relu_eq_add_abs (F B)

def starBooleanCoefficient (prime : Bool) (B : Finset (Fin 5)) (i : Fin 4) : ℤ :=
  if prime then
    if (4 : Fin 5)∈B ∧ i.castSucc∉B then -1 else 0
  else if (4 : Fin 5)∉B ∧ i.castSucc∈B then 1 else 0

theorem starBooleanCoefficient_mobius_zero : ∀ (prime : Bool) (i : Fin 4),
    (∑ B : Finset (Fin 5), topMobiusSign B*starBooleanCoefficient prime B i)=0 := by decide

theorem starSetFunction_linear_coefficients (v v' : Fin 4→ℝ) (B : Finset (Fin 5)) :
    starSetFunction v v' B=
      ∑ i : Fin 4, ((starBooleanCoefficient false B i : ℝ)*v i+
        (starBooleanCoefficient true B i : ℝ)*v' i) := by
  unfold starSetFunction
  by_cases hc : (4 : Fin 5)∈B
  · simp only [if_pos hc]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.castSucc∈B <;> simp [starBooleanCoefficient,hc,hi]
  · simp only [if_neg hc]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.castSucc∈B <;> simp [starBooleanCoefficient,hc,hi]

theorem topMobius_starSetFunction (v v' : Fin 4→ℝ) :
    topMobius (starSetFunction v v')=0 := by
  have he : starSetFunction v v' = fun B =>
      ∑ i : Fin 4, ((starBooleanCoefficient false B i : ℝ)*v i+
        (starBooleanCoefficient true B i : ℝ)*v' i) := by
    funext B
    exact starSetFunction_linear_coefficients v v' B
  rw [he,topMobius_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [topMobius_add]
  have hc : ∀ prime : Bool,
      topMobius (fun B => (starBooleanCoefficient prime B i : ℝ))=0 := by
    intro prime
    have hh := congrArg (fun q : ℤ => (q : ℝ)) (starBooleanCoefficient_mobius_zero prime i)
    simpa only [topMobius,Int.cast_sum,Int.cast_mul,Int.cast_zero] using hh
  have hv : ∀ (prime : Bool) (a : ℝ),
      topMobius (fun B => (starBooleanCoefficient prime B i : ℝ)*a)=0 := by
    intro prime a
    simpa only [mul_comm,topMobius_mul,hc,mul_zero]
  rw [hv,hv,add_zero]

noncomputable def booleanOR (B : Finset (Fin 5)) : ℝ := if B=∅ then 0 else 1

theorem topMobius_booleanOR : topMobius booleanOR=1 := by
  have hh : (∑ B : Finset (Fin 5), topMobiusSign B*(if B=∅ then 0 else 1))=(1:ℤ) := by decide
  have he := congrArg (fun q : ℤ => (q : ℝ)) hh
  simpa only [topMobius,booleanOR,Int.cast_sum,Int.cast_mul,apply_ite,
    Int.cast_zero,Int.cast_one] using he

#print axioms sum_weighted_setFunctionChain
#print axioms topMobius_starSetFunction
#print axioms topMobius_booleanOR
end MaxCaterpillar.Frontier.StarCertificate
