import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset

/-! # Isolated low-rank gaps and their actual adjacent tail slots -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {m : ℕ}

noncomputable def allGapAdjacencies : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p => p.1.val + 1 = p.2.val)

noncomputable def selectedGapAdjacencies (Γ : Finset (Fin m)) :
    Finset (Fin m × Fin m) := by
  classical
  exact allGapAdjacencies.filter (fun p => p.1 ∈ Γ ∧ p.2 ∈ Γ)

/-- The anchor gap is excluded; an isolated final gap is retained. -/
noncomputable def isolatedGaps (Γ : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact Γ.filter (fun g => 0 < g.val ∧
    ∀ h ∈ Γ, h.val + 1 ≠ g.val ∧ g.val + 1 ≠ h.val)

@[simp] theorem mem_allGapAdjacencies (a b : Fin m) :
    (a,b) ∈ allGapAdjacencies ↔ a.val + 1 = b.val := by
  classical
  simp [allGapAdjacencies]

@[simp] theorem mem_selectedGapAdjacencies (a b : Fin m) (Γ : Finset (Fin m)) :
    (a,b) ∈ selectedGapAdjacencies Γ ↔ a.val + 1 = b.val ∧ a ∈ Γ ∧ b ∈ Γ := by
  classical
  simp only [selectedGapAdjacencies,Finset.mem_filter,mem_allGapAdjacencies]

@[simp] theorem mem_isolatedGaps (g : Fin m) (Γ : Finset (Fin m)) :
    g ∈ isolatedGaps Γ ↔ g ∈ Γ ∧ 0 < g.val ∧
      ∀ h ∈ Γ, h.val + 1 ≠ g.val ∧ g.val + 1 ≠ h.val := by
  classical
  simp only [isolatedGaps,Finset.mem_filter]

def isolatedGapPredecessor (g : Fin m) : Fin m :=
  ⟨g.val - 1,lt_of_le_of_lt (Nat.sub_le _ _) g.isLt⟩

lemma isolatedGapPredecessor_succ (g : Fin m) (hg : 0 < g.val) :
    (isolatedGapPredecessor g).val + 1 = g.val :=
  Nat.sub_add_cancel (Nat.succ_le_of_lt hg)

/-- False is the left tail position, true the right tail position. -/
def isolatedGapEndpoint (Γ : Finset (Fin m))
    (p : ↥(isolatedGaps Γ) × Bool) : Fin m :=
  match p.2 with
  | false => isolatedGapPredecessor p.1.val
  | true => p.1.val

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
