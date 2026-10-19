import MaxNN.Constructions.Paramid.Caterpillar.Corrections.AbsorbHinges
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Reversal

/-!
# Quadratically many absorbable hinge keys

For every ordered pair of distinct standard-simplex vertices, a full-spine
word has those vertices as its terminal and apex endpoints.  Its all-zero
face is the corresponding empty-label hinge key.  These ordered-pair keys are
distinct, survive label normalization unchanged, and are therefore all
removed by `essentialKeys`.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidChain

noncomputable section

variable {r : ℕ}

/-- An apex `b` together with a distinct terminal vertex `a`. -/
abbrev OrderedHingeEndpoint (r : ℕ) :=
  Σ b : Fin (r + 1 + 1), {a : Fin (r + 1 + 1) // a ≠ b}

def orderedHingeKey (p : OrderedHingeEndpoint r) : RealKey (r + 1) :=
  (toR (vtx p.2.1) - toR (vtx p.1), ∅)

/-- A permutation sending position zero to the chosen apex and the final
position to the chosen terminal vertex. -/
def endpointPerm (p : OrderedHingeEndpoint r) :
    Equiv.Perm (Fin (r + 1 + 1)) :=
  let σ : Equiv.Perm (Fin (r + 1 + 1)) := Equiv.swap 0 p.1
  σ.trans (Equiv.swap (σ (Fin.last (r + 1))) p.2.1)

theorem endpointPerm_zero (p : OrderedHingeEndpoint r) : endpointPerm p 0 = p.1 := by
  let σ : Equiv.Perm (Fin (r + 1 + 1)) := Equiv.swap 0 p.1
  have hlast0 : Fin.last (r + 1) ≠ (0 : Fin (r + 1 + 1)) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_last, Fin.val_zero]
    omega
  have hs0 : σ 0 = p.1 := by
    exact Equiv.swap_apply_left 0 p.1
  have hsb : σ (Fin.last (r + 1)) ≠ p.1 := by
    intro h
    apply hlast0
    apply σ.injective
    rw [h, hs0]
  unfold endpointPerm
  change (Equiv.swap (σ (Fin.last (r + 1))) p.2.1) (σ 0) = p.1
  rw [hs0]
  exact Equiv.swap_apply_of_ne_of_ne hsb.symm p.2.2.symm

theorem endpointPerm_last (p : OrderedHingeEndpoint r) :
    endpointPerm p (Fin.last (r + 1)) = p.2.1 := by
  unfold endpointPerm
  change (Equiv.swap
    ((Equiv.swap 0 p.1) (Fin.last (r + 1))) p.2.1)
      ((Equiv.swap 0 p.1) (Fin.last (r + 1))) = p.2.1
  exact Equiv.swap_apply_left _ _

noncomputable def endpointPathWord (hr : 1 ≤ r) (p : OrderedHingeEndpoint r) :
    WordIndex r :=
  pathWord hr (endpointPerm p)

theorem endpointPathWord_gamma (hr : 1 ≤ r) (p : OrderedHingeEndpoint r) :
    wordGamma (endpointPathWord hr p) =
      toR (vtx p.2.1) - toR (vtx p.1) := by
  unfold wordGamma wordBase wordApex endpointPathWord pathWord
  rw [lastHead_cutPositions hr]
  rw [show (Fin.last r).succ = Fin.last (r + 1) by apply Fin.ext; rfl]
  rw [endpointPerm_last, endpointPerm_zero]

theorem normalizedKey_empty (γ : Fin (r + 1) → ℝ) :
    normalizedKey (γ, ∅) = (γ, ∅) := by
  classical
  unfold normalizedKey
  simp only [Finset.filter_empty, Finset.sum_empty, add_zero, Finset.image_empty]

theorem emptyLabelKey_mem_faceKeys (γ : Fin (r + 1) → ℝ)
    (V : Finset (Fin (r + 1) → ℝ)) : (γ, ∅) ∈ faceKeys γ V := by
  classical
  simpa only [Finset.sum_empty, add_zero] using
    (mem_faceKeys_of_disjoint
      (γ := γ) (V := V) (P := ∅) (Z := ∅)
      (Finset.empty_subset _) (Finset.empty_subset _)
      (Finset.disjoint_empty_left _))

theorem orderedHingeKey_mem_correctionKeys (hr : 1 ≤ r)
    (p : OrderedHingeEndpoint r) : orderedHingeKey p ∈ correctionKeys r := by
  classical
  let w := endpointPathWord hr p
  have hc : (wordGamma w, ∅) ∈ correctionKeys r :=
    faceKeys_subset_correctionKeys w
      (emptyLabelKey_mem_faceKeys (wordGamma w) (wordLabels w))
  rw [show wordGamma w = toR (vtx p.2.1) - toR (vtx p.1) from
    endpointPathWord_gamma hr p] at hc
  simpa only [orderedHingeKey] using hc

theorem orderedHingeKey_mem_normalizedKeys (hr : 1 ≤ r)
    (p : OrderedHingeEndpoint r) : orderedHingeKey p ∈ normalizedKeys r := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨orderedHingeKey p, orderedHingeKey_mem_correctionKeys hr p, ?_⟩
  exact normalizedKey_empty _

theorem orderedHingeKey_injective : Function.Injective (orderedHingeKey (r := r)) := by
  intro p q hpq
  have hγ := congrArg Prod.fst hpq
  have hend := simplex_difference_endpoints p.2.2 hγ
  obtain ⟨b, a⟩ := p
  obtain ⟨d, c⟩ := q
  dsimp only at hend
  cases hend.2
  have hac : a = c := Subtype.ext hend.1
  cases hac
  rfl

/-- The finite set of all distinct ordered-pair hinge keys. -/
noncomputable def orderedHingeKeys (r : ℕ) : Finset (RealKey (r + 1)) :=
  Finset.univ.image orderedHingeKey

theorem card_OrderedHingeEndpoint (r : ℕ) :
    Fintype.card (OrderedHingeEndpoint r) = (r + 1 + 1) * (r + 1) := by
  classical
  have hfiber : ∀ b : Fin (r + 1 + 1),
      Fintype.card {a : Fin (r + 1 + 1) // a ≠ b} = r + 1 := by
    intro b
    calc
      Fintype.card {a : Fin (r + 1 + 1) // a ≠ b} =
          Fintype.card (Fin (r + 1 + 1)) - 1 := Set.card_ne_eq b
      _ = r + 1 := by simp only [Fintype.card_fin]; omega
  rw [Fintype.card_sigma]
  simp_rw [hfiber]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

theorem orderedHingeKeys_card (r : ℕ) :
    (orderedHingeKeys r).card = (r + 1 + 1) * (r + 1) := by
  classical
  unfold orderedHingeKeys
  rw [Finset.card_image_of_injective _ orderedHingeKey_injective,
    Finset.card_univ, card_OrderedHingeEndpoint]

theorem orderedHingeKeys_subset_hingeKeys_normalizedKeys (hr : 1 ≤ r) :
    orderedHingeKeys r ⊆ hingeKeys (normalizedKeys r) := by
  classical
  intro k hk
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨orderedHingeKey_mem_normalizedKeys hr p, rfl, ?_⟩
  exact ⟨p.2.1, p.1, rfl⟩

theorem orderedHingeCount_le (hr : 1 ≤ r) :
    (r + 1 + 1) * (r + 1) ≤ (hingeKeys (normalizedKeys r)).card := by
  classical
  rw [← orderedHingeKeys_card r]
  exact Finset.card_le_of_subset
    (orderedHingeKeys_subset_hingeKeys_normalizedKeys hr)

/-- Removing the empty-label hinge keys saves at least `N(N-1)` dictionary
rows, where `N = r+2` is the input arity. -/
theorem essentialNormalizedKeys_card_le_sub_orderedHinges (hr : 1 ≤ r) :
    (essentialKeys (normalizedKeys r)).card ≤
      (normalizedKeys r).card - (r + 1 + 1) * (r + 1) := by
  apply Nat.le_sub_of_add_le
  calc
    (essentialKeys (normalizedKeys r)).card + (r + 1 + 1) * (r + 1) ≤
        (essentialKeys (normalizedKeys r)).card +
          (hingeKeys (normalizedKeys r)).card :=
      Nat.add_le_add_left (orderedHingeCount_le hr) _
    _ = (normalizedKeys r).card :=
      essentialKeys_card_add_hingeKeys_card (normalizedKeys r)

end

end MaxNN.Caterpillar.Corrections
