import Mathlib.Data.Fin.Interval
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Prod

/-! # Actual gap-run geometry for the good event

Tail labels occupy positions 1,...,m. A `Fin m` tail position has value
one less than its paper position. Gap g has paper index g.val+1. Thus the
gaps between tail positions a,b are `Ioc (min a b) (max a b)`, while the
gaps joining the anchor to a are `Iic a`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators

variable {m : ℕ}

def tailInterval (a b : Fin m) : Finset (Fin m) :=
  Finset.Ioc (min a b) (max a b)

def TailSameRun (Γ : Finset (Fin m)) (a b : Fin m) : Prop :=
  tailInterval a b ⊆ Γ

def AnchorSameRun (Γ : Finset (Fin m)) (a : Fin m) : Prop :=
  Finset.Iic a ⊆ Γ

def TailAdjacent (Γ : Finset (Fin m)) (a b : Fin m) : Prop :=
  (a.val + 1 = b.val ∧ b ∈ Γ) ∨ (b.val + 1 = a.val ∧ a ∈ Γ)

noncomputable def adjacentPairs (Γ : Finset (Fin m)) : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p => TailAdjacent Γ p.1 p.2)

noncomputable def orderedRunPairs (Γ : Finset (Fin m)) : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ TailSameRun Γ p.1 p.2)

noncomputable def anchoredRun (Γ : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun a => AnchorSameRun Γ a)

@[simp] theorem tailInterval_comm (a b : Fin m) : tailInterval a b = tailInterval b a := by
  simp only [tailInterval, min_comm, max_comm]

theorem tailSameRun_mono {Γ Δ : Finset (Fin m)} (h : Γ ⊆ Δ)
    {a b : Fin m} (hab : TailSameRun Γ a b) : TailSameRun Δ a b :=
  Finset.Subset.trans hab h

theorem anchorSameRun_mono {Γ Δ : Finset (Fin m)} (h : Γ ⊆ Δ)
    {a : Fin m} (ha : AnchorSameRun Γ a) : AnchorSameRun Δ a :=
  Finset.Subset.trans ha h

private def gapPredecessor (g : Fin m) : Fin m :=
  ⟨g.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) g.isLt⟩

private def orientedGapPair (p : Fin m × Bool) : Fin m × Fin m :=
  if p.2 then (p.1, gapPredecessor p.1) else (gapPredecessor p.1, p.1)

/-- There are at most two oriented adjacent tail pairs for each selected
gap. The anchor gap is harmlessly overcounted in this upper bound. -/
theorem adjacentPairs_card_le (Γ : Finset (Fin m)) :
    (adjacentPairs Γ).card ≤ 2 * Γ.card := by
  classical
  have hsub : adjacentPairs Γ ⊆ (Γ.product Finset.univ).image orientedGapPair := by
    intro p hp
    have hh : TailAdjacent Γ p.1 p.2 := (Finset.mem_filter.mp hp).2
    rcases hh with ⟨hab, hb⟩ | ⟨hba, ha⟩
    · have hpred : gapPredecessor p.2 = p.1 := by
        apply Fin.ext
        change p.2.val - 1 = p.1.val
        rw [← hab]
        simp
      apply Finset.mem_image.mpr
      refine ⟨(p.2, false), Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩, ?_⟩
      simp [orientedGapPair, hpred]
    · have hpred : gapPredecessor p.1 = p.2 := by
        apply Fin.ext
        change p.1.val - 1 = p.2.val
        rw [← hba]
        simp
      apply Finset.mem_image.mpr
      refine ⟨(p.1, true), Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, ?_⟩
      simp only [orientedGapPair, if_true, hpred, Prod.mk.eta]
  calc
    _ ≤ ((Γ.product Finset.univ).image orientedGapPair).card := Finset.card_le_of_subset hsub
    _ ≤ (Γ.product (Finset.univ : Finset Bool)).card := Finset.card_image_le
    _ = 2 * Γ.card := by
      change (Γ ×ˢ (Finset.univ : Finset Bool)).card = 2 * Γ.card
      rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
      exact Nat.mul_comm _ _

/-- The four labels are distinct because they are supplied by an actual
embedding. Forgetting distinctness only increases the product count. -/
noncomputable def caseAPlacements (Γ : Finset (Fin m)) : Finset (Fin 4 ↪ Fin m) := by
  classical
  exact Finset.univ.filter (fun q => TailAdjacent Γ (q 0) (q 1) ∧
    TailSameRun Γ (q 2) (q 3))

noncomputable def caseBPlacements (Γ : Finset (Fin m)) : Finset (Fin 3 ↪ Fin m) := by
  classical
  exact Finset.univ.filter (fun q => TailAdjacent Γ (q 0) (q 1) ∧ AnchorSameRun Γ (q 2))

theorem caseAPlacements_card_le (Γ : Finset (Fin m)) :
    (caseAPlacements Γ).card ≤ 2 * Γ.card * (orderedRunPairs Γ).card := by
  classical
  let f : (Fin 4 ↪ Fin m) → (Fin m × Fin m) × (Fin m × Fin m) :=
    fun q => ((q 0, q 1), (q 2, q 3))
  have hinj : Function.Injective f := by
    intro a b hab
    apply Function.Embedding.ext
    intro i
    have h0 := congrArg (fun p => p.1.1) hab
    have h1 := congrArg (fun p => p.1.2) hab
    have h2 := congrArg (fun p => p.2.1) hab
    have h3 := congrArg (fun p => p.2.2) hab
    fin_cases i <;> assumption
  have hsub : (caseAPlacements Γ).image f ⊆ (adjacentPairs Γ).product (orderedRunPairs Γ) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hh := (Finset.mem_filter.mp hq).2
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, hh.2⟩
      exact fun he => (by decide : (2 : Fin 4) ≠ 3) (q.injective he)
  calc
    _ = ((caseAPlacements Γ).image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((adjacentPairs Γ).product (orderedRunPairs Γ)).card := Finset.card_le_of_subset hsub
    _ = (adjacentPairs Γ).card * (orderedRunPairs Γ).card := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul_right _ (adjacentPairs_card_le Γ)

theorem caseBPlacements_card_le (Γ : Finset (Fin m)) :
    (caseBPlacements Γ).card ≤ 2 * Γ.card * (anchoredRun Γ).card := by
  classical
  let f : (Fin 3 ↪ Fin m) → (Fin m × Fin m) × Fin m :=
    fun q => ((q 0, q 1), q 2)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Function.Embedding.ext
    intro i
    have h0 := congrArg (fun p => p.1.1) hab
    have h1 := congrArg (fun p => p.1.2) hab
    have h2 := congrArg (fun p => p.2) hab
    fin_cases i <;> assumption
  have hsub : (caseBPlacements Γ).image f ⊆ (adjacentPairs Γ).product (anchoredRun Γ) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hh := (Finset.mem_filter.mp hq).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.2⟩⟩
  calc
    _ = ((caseBPlacements Γ).image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((adjacentPairs Γ).product (anchoredRun Γ)).card := Finset.card_le_of_subset hsub
    _ = (adjacentPairs Γ).card * (anchoredRun Γ).card := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul_right _ (adjacentPairs_card_le Γ)

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
