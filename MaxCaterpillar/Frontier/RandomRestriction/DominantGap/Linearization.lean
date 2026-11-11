import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model
import Mathlib.Data.Fintype.BigOperators

/-! # Exact active-first linearization of the indexed skip model

A second preactivation is a genuine linear form at each point once its actual
first-layer signs are fixed. Every effective row is an explicit finite linear
combination of the original first rows and the original second linear skip.
No sign assumptions on any weights are used.

The final adapters only specialize a supplied universal linear-form criterion
to this finite family. No restriction-survival statement is built into the
network model or assumed of an actual nonlinear preactivation.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators

variable {N h₁ h₂ : ℕ}

/-- Strictly active first-neuron pattern at one actual input. Zero first forms
are inactive; their ReLU value is nevertheless treated exactly. -/
noncomputable def activePattern (net : NormalizedNetwork N h₁ h₂) (q : Point N) :
    Fin h₁→Bool := by
  classical
  exact fun j => decide (0<lin (net.A j) q)

@[simp] theorem activePattern_eq_true (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (j : Fin h₁) :
    activePattern net q j=true ↔ 0<lin (net.A j) q := by
  classical
  simp [activePattern]

/-- The original linear skip plus precisely the active first-row contributions. -/
noncomputable def effectiveRow (net : NormalizedNetwork N h₁ h₂)
    (b : Fin h₁→Bool) (k : Fin h₂) : Point N := by
  classical
  exact net.U k+∑ j in Finset.univ.filter (fun j => b j=true),net.W k j • net.A j

/-- Linear readout of any candidate pattern, valid on all inputs. -/
theorem lin_effectiveRow (net : NormalizedNetwork N h₁ h₂)
    (b : Fin h₁→Bool) (k : Fin h₂) (q : Point N) :
    lin (effectiveRow net b k) q=lin (net.U k) q+
      ∑ j in Finset.univ.filter (fun j => b j=true),net.W k j*lin (net.A j) q := by
  classical
  rw [effectiveRow,lin_add_left,lin_sum_left]
  simp only [lin_smul_left]

/-- A proposed pattern is sufficient only after proving it equals the actual
strict first-layer signs. The weighted identity then follows exactly. -/
theorem inner_eq_lin_effectiveRow_of_pattern (net : NormalizedNetwork N h₁ h₂)
    (b : Fin h₁→Bool) (k : Fin h₂) (q : Point N)
    (hb : ∀ j,b j=true ↔ 0<lin (net.A j) q) :
    net.inner k q=lin (effectiveRow net b k) q := by
  classical
  rw [lin_effectiveRow,NormalizedNetwork.inner]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : 0<lin (net.A j) q
  · rw [if_pos ((hb j).mpr hp),relu_of_nonneg hp.le]
  · rw [if_neg (fun h => hp ((hb j).mp h)),relu_of_nonpos (not_lt.mp hp),mul_zero]

/-- The exact coefficient row selected by the actual first activations. -/
noncomputable def actualEffectiveRow (net : NormalizedNetwork N h₁ h₂)
    (k : Fin h₂) (q : Point N) : Point N := effectiveRow net (activePattern net q) k

theorem inner_eq_lin_actualEffectiveRow (net : NormalizedNetwork N h₁ h₂)
    (k : Fin h₂) (q : Point N) :
    net.inner k q=lin (actualEffectiveRow net k q) q :=
  inner_eq_lin_effectiveRow_of_pattern net (activePattern net q) k q
    (fun j => activePattern_eq_true net q j)

/-- Zero sums are preserved by every pattern's arbitrary real linear combination. -/
theorem effectiveRow_zero_sum_of_rows (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j,∑ i,net.A j i=0) (hU : ∀ k,∑ i,net.U k i=0)
    (b : Fin h₁→Bool) (k : Fin h₂) : ∑ i,effectiveRow net b k i=0 := by
  classical
  have hs : (∑ i : Fin N,
      (∑ j in Finset.univ.filter (fun j => b j=true),net.W k j • net.A j) i)=0 := by
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,hA]
    simp
  simp only [effectiveRow,Pi.add_apply,Finset.sum_add_distrib]
  rw [hU,hs]
  simp

theorem effectiveRow_zero_sum (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (b : Fin h₁→Bool) (k : Fin h₂) :
    ∑ i,effectiveRow net b k i=0 :=
  effectiveRow_zero_sum_of_rows net hn.1 hn.2.1 b k

/-- Finite index set covering every possible effective second row. Repeated
rows are retained, so no equality decision or normalization of real vectors is required. -/
abbrev EffectiveRowIndex (h₁ h₂ : ℕ) := (Fin h₁→Bool)×Fin h₂

noncomputable def effectiveRowFamily (net : NormalizedNetwork N h₁ h₂)
    (s : EffectiveRowIndex h₁ h₂) : Point N := effectiveRow net s.1 s.2

theorem effectiveRowIndex_card : Fintype.card (EffectiveRowIndex h₁ h₂)=2^h₁*h₂ := by
  simp [EffectiveRowIndex]

theorem actualEffectiveRow_mem_family (net : NormalizedNetwork N h₁ h₂)
    (k : Fin h₂) (q : Point N) : actualEffectiveRow net k q∈Set.range (effectiveRowFamily net) :=
  ⟨(activePattern net q,k),rfl⟩

theorem effectiveRowFamily_zero_sum (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (s : EffectiveRowIndex h₁ h₂) :
    ∑ i,effectiveRowFamily net s i=0 := effectiveRow_zero_sum net hn s.1 s.2

/-- Pointwise adapter for any proved dot-product/restriction criterion covering
all patterns. The restriction may itself depend on the external parameter. -/
theorem inner_eq_zero_iff_of_family_criterion_at {τ γ : Type*} [Zero γ]
    (net : NormalizedNetwork N h₁ h₂) (q : τ→Point N) (restriction : τ→Point N→γ)
    (t : τ) (k : Fin h₂)
    (hcriterion : ∀ s : EffectiveRowIndex h₁ h₂,
      lin (effectiveRowFamily net s) (q t)=0 ↔ restriction t (effectiveRowFamily net s)=0) :
    net.inner k (q t)=0 ↔ restriction t (actualEffectiveRow net k (q t))=0 := by
  rw [inner_eq_lin_actualEffectiveRow]
  exact hcriterion (activePattern net (q t),k)

/-- Universal-parameter form: the changing actual pattern is selected inside
the proof, rather than assumed to remain fixed as the parameter changes. -/
theorem inner_eq_zero_iff_of_family_criterion {τ γ : Type*} [Zero γ]
    (net : NormalizedNetwork N h₁ h₂) (q : τ→Point N) (restriction : τ→Point N→γ)
    (hcriterion : ∀ t (s : EffectiveRowIndex h₁ h₂),
      lin (effectiveRowFamily net s) (q t)=0 ↔ restriction t (effectiveRowFamily net s)=0)
    (t : τ) (k : Fin h₂) :
    net.inner k (q t)=0 ↔ restriction t (actualEffectiveRow net k (q t))=0 :=
  inner_eq_zero_iff_of_family_criterion_at net q restriction t k (hcriterion t)

theorem inner_ne_zero_iff_of_family_criterion_at {τ γ : Type*} [Zero γ]
    (net : NormalizedNetwork N h₁ h₂) (q : τ→Point N) (restriction : τ→Point N→γ)
    (t : τ) (k : Fin h₂)
    (hcriterion : ∀ s : EffectiveRowIndex h₁ h₂,
      lin (effectiveRowFamily net s) (q t)=0 ↔ restriction t (effectiveRowFamily net s)=0) :
    net.inner k (q t)≠0 ↔ restriction t (actualEffectiveRow net k (q t))≠0 :=
  not_congr (inner_eq_zero_iff_of_family_criterion_at net q restriction t k hcriterion)
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
