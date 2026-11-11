import MaxCaterpillar.Frontier.StarCertificate.XiQuadKappa
import MaxCaterpillar.Frontier.StarCertificate.XiFastSelectors
import MaxCaterpillar.Frontier.StarCertificate.XiInteger

/-! # One compiled selector row and its independent bounded checker -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate

structure CompiledSelectorRow where
  chain : Fin 4 → FormRef 15
  coarse : Fin 10 → FormRef 15
  chainCoefficients : Fin 4 → IntegerQuad

def CompiledSelectorRow.Valid (T : Fin 16) (p : Fin 120) (row : CompiledSelectorRow) : Prop :=
  (∀ j,row.chain j=maskedChain T p j) ∧
  (∀ j,row.coarse j=maskedCoarse T p j) ∧
  ∀ j i,(row.chainCoefficients j).toForm i=
    (maskedChain T p j).integerForm starIntegerSubsetForms i

/-- All runtime masks/bits are absent from the compiled row. This independent
checker compares its literals to the original mask semantics. -/
def compiledSelectorRowCheck (T : Fin 16) (p : Fin 120) (row : CompiledSelectorRow) : Bool :=
  match row with
  | ⟨chain,coarse,coeffs⟩ =>
    finAll 4 (fun j => decide (chain j=fastMaskedChain T p j)) &&
    (finAll 10 (fun j => decide (coarse j=fastMaskedCoarse T p j)) &&
    finAll 4 (fun j => finAll 4 (fun i => decide
      ((coeffs j).toForm i=(chain j).integerForm starIntegerSubsetForms i))))

theorem compiledSelectorRowCheck_sound (T : Fin 16) (p : Fin 120) (row : CompiledSelectorRow)
    (h : compiledSelectorRowCheck T p row=true) : row.Valid T p := by
  cases row with
  | mk chain coarse coeffs =>
    simp only [compiledSelectorRowCheck,Bool.and_eq_true] at h
    have hchain : ∀ j,chain j=maskedChain T p j := fun j =>
      (of_decide_eq_true ((finAll_eq_true 4 _).mp h.1 j)).trans (fastMaskedChain_eq T p j)
    have hcoarse : ∀ j,coarse j=maskedCoarse T p j := fun j =>
      (of_decide_eq_true ((finAll_eq_true 10 _).mp h.2.1 j)).trans (fastMaskedCoarse_eq T p j)
    refine ⟨hchain,hcoarse,fun j i => ?_⟩
    change (coeffs j).toForm i=(maskedChain T p j).integerForm starIntegerSubsetForms i
    rw [← hchain j]
    exact of_decide_eq_true ((finAll_eq_true 4 _).mp ((finAll_eq_true 4 _).mp h.2.2 j) i)

/-- Twelve blocks of ten permutations bound each arithmetic proof chunk. -/
def selectorBlockPermutation (b : Fin 12) (j : Fin 10) : Fin 120 :=
  ⟨b.val*10+j.val,by
    calc
      b.val*10+j.val < b.val*10+10 := Nat.add_lt_add_left j.isLt _
      _ = (b.val+1)*10 := by ring
      _ ≤ 120 := Nat.mul_le_mul_right 10 (Nat.succ_le_of_lt b.isLt)⟩

theorem selectorBlockPermutation_covers : ∀ p : Fin 120,
    ∃ b : Fin 12,∃ j : Fin 10,selectorBlockPermutation b j=p := by decide

#print axioms compiledSelectorRowCheck_sound
#print axioms selectorBlockPermutation_covers
end MaxCaterpillar.Frontier.StarCertificate
