import MaxCaterpillar.CountCubic.FullCoords

/-!
# The caterpillar tree of a decorated word, in full labels

A word `w = (π, S) : WordIndex r` places the labels `0, …, r+1` (full
coordinates) at word positions: the apex is `π 0`, and base position
`i : Fin (r+1)` carries the label `π i.succ`.  The base positions form a
caterpillar tree rooted at position `0`: every base position `j.succ`
(`j : Fin r`) has the parent position `parent S j.succ`; the spine positions
are `insert 0 S` and the last spine position is `lastHead S`.

Tree edge `j : Fin r` joins the parent label `parV w j` and the child label
`childV w j`; its word label is `edgeVecs … j = u_{parV} - u_{childV}`.
A face state `τ` assigns each edge one of three states (`edgeState`):
`0` omitted, `1` linear (frozen at the identity), `2` hinge (active).
-/

open BigOperators

namespace MaxCaterpillar.CountCubic

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain

variable {r : ℕ}

/-- The apex label. -/
def apexV (w : WordIndex r) : Fin (r + 1 + 1) := w.1 0

/-- The label at base position `i`. -/
def baseV (w : WordIndex r) (i : Fin (r + 1)) : Fin (r + 1 + 1) := w.1 i.succ

/-- The last spine label. -/
def lastV (w : WordIndex r) : Fin (r + 1 + 1) := baseV w (lastHead w.2.1)

/-- The parent label of tree edge `j`. -/
def parV (w : WordIndex r) (j : Fin r) : Fin (r + 1 + 1) := baseV w (parent w.2.1 j.succ)

/-- The child label of tree edge `j`. -/
def childV (w : WordIndex r) (j : Fin r) : Fin (r + 1 + 1) := baseV w j.succ

/-- The lower and upper end of tree edge `j` (in the label order). -/
def lowV (w : WordIndex r) (j : Fin r) : Fin (r + 1 + 1) := min (parV w j) (childV w j)

def highV (w : WordIndex r) (j : Fin r) : Fin (r + 1 + 1) := max (parV w j) (childV w j)

/-- The spine labels. -/
def spineV (w : WordIndex r) : Finset (Fin (r + 1 + 1)) :=
  (insert 0 w.2.1).image (baseV w)

/-- The state of tree edge `j` under the face state `τ`. -/
noncomputable def edgeState (w : WordIndex r) (τ : wordLabels w → Fin 3) (j : Fin r) : Fin 3 :=
  keyExt (wordLabels w) τ (edgeVecs (wordBase w) w.2.1 j)

/-- The normalized face key of the word `w` with face state `τ`. -/
noncomputable def wordFaceKey (w : WordIndex r) (τ : wordLabels w → Fin 3) : RealKey (r + 1) :=
  normalizedKey (faceKey (wordGamma w) (wordLabels w) τ)

theorem exists_word_of_mem_normalizedKeys {k : RealKey (r + 1)} (hk : k ∈ normalizedKeys r) :
    ∃ (w : WordIndex r) (τ : wordLabels w → Fin 3), k = wordFaceKey w τ := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨q', hq', hqq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hq'
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hqq
  exact ⟨w, τ, rfl⟩

theorem wordFaceKey_mem_normalizedKeys (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    wordFaceKey w τ ∈ normalizedKeys r :=
  Finset.mem_image.mpr ⟨_, faceKeys_subset_correctionKeys w
    (Finset.mem_image.mpr ⟨τ, Finset.mem_univ τ, rfl⟩), rfl⟩

/-! ## Elementary facts about the labels -/

theorem baseV_injective (w : WordIndex r) : Function.Injective (baseV w) :=
  w.1.injective.comp (Fin.succ_injective _)

theorem apexV_ne_baseV (w : WordIndex r) (i : Fin (r + 1)) : apexV w ≠ baseV w i := by
  intro h
  exact Fin.succ_ne_zero i (w.1.injective h).symm

theorem apexV_ne_parV (w : WordIndex r) (j : Fin r) : apexV w ≠ parV w j :=
  apexV_ne_baseV w _

theorem apexV_ne_childV (w : WordIndex r) (j : Fin r) : apexV w ≠ childV w j :=
  apexV_ne_baseV w _

theorem apexV_ne_lastV (w : WordIndex r) : apexV w ≠ lastV w :=
  apexV_ne_baseV w _

theorem childV_injective (w : WordIndex r) : Function.Injective (childV w) :=
  (baseV_injective w).comp (Fin.succ_injective _)

theorem parent_succ_lt (S : Finset (Fin (r + 1))) (j : Fin r) : parent S j.succ < j.succ :=
  parent_lt (Fin.succ_pos j)

theorem parV_ne_childV (w : WordIndex r) (j : Fin r) : parV w j ≠ childV w j := by
  intro h
  exact (ne_of_lt (parent_succ_lt w.2.1 j)) (baseV_injective w h)

/-- Every label other than the apex is a base label. -/
theorem exists_baseV_of_ne_apexV (w : WordIndex r) {o : Fin (r + 1 + 1)} (ho : o ≠ apexV w) :
    ∃ i, baseV w i = o := by
  obtain ⟨p, rfl⟩ := w.1.surjective o
  refine Fin.cases (fun h => ?_) (fun i _ => ⟨i, rfl⟩) p ho
  exact absurd rfl h

theorem edgeVecs_eq (w : WordIndex r) (j : Fin r) :
    edgeVecs (wordBase w) w.2.1 j = toR (vtx (parV w j)) - toR (vtx (childV w j)) := rfl

theorem edgeVecs_word_injective (w : WordIndex r) :
    Function.Injective (edgeVecs (wordBase w) w.2.1) :=
  edgeVecs_simplex_injective (fun i => w.1 i.succ)
    (w.1.injective.comp (Fin.succ_injective (r + 1))) w.2.1

theorem lowV_lt_highV (w : WordIndex r) (j : Fin r) : lowV w j < highV w j := by
  unfold lowV highV
  rcases lt_or_gt_of_ne (parV_ne_childV w j) with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact h

theorem reverseLabel_edge_iff (w : WordIndex r) (j : Fin r) :
    reverseLabel (edgeVecs (wordBase w) w.2.1 j) ↔ childV w j < parV w j := by
  rw [edgeVecs_eq]
  constructor
  · rintro ⟨a, b, hba, he⟩
    obtain ⟨rfl, rfl⟩ := simplex_difference_endpoints (parV_ne_childV w j) he
    exact hba
  · intro h
    exact ⟨_, _, h, rfl⟩

theorem orientedLabel_edge (w : WordIndex r) (j : Fin r) :
    orientedLabel (edgeVecs (wordBase w) w.2.1 j) =
      toR (vtx (lowV w j)) - toR (vtx (highV w j)) := by
  unfold orientedLabel lowV highV
  by_cases h : childV w j < parV w j
  · rw [if_pos ((reverseLabel_edge_iff w j).mpr h), edgeVecs_eq, neg_sub,
      min_eq_right h.le, max_eq_left h.le]
  · rw [if_neg (fun h' => h ((reverseLabel_edge_iff w j).mp h')), edgeVecs_eq]
    have h' : parV w j ≤ childV w j := not_lt.mp h
    rw [min_eq_left h', max_eq_right h']

/-- In a tree, the two ends determine the edge. -/
theorem edge_eq_of_low_high (w : WordIndex r) {j j' : Fin r}
    (hl : lowV w j = lowV w j') (hh : highV w j = highV w j') : j = j' := by
  have key : ¬ (parV w j = childV w j' ∧ childV w j = parV w j') := by
    rintro ⟨h1, h2⟩
    have e1 := baseV_injective w h1
    have e2 := baseV_injective w h2
    have l1 := parent_succ_lt w.2.1 j
    have l2 := parent_succ_lt w.2.1 j'
    rw [e1] at l1
    rw [← e2] at l2
    exact lt_asymm l1 l2
  unfold lowV at hl
  unfold highV at hh
  rcases lt_or_gt_of_ne (parV_ne_childV w j) with h | h <;>
    rcases lt_or_gt_of_ne (parV_ne_childV w j') with h' | h'
  · rw [min_eq_left h.le, min_eq_left h'.le] at hl
    rw [max_eq_right h.le, max_eq_right h'.le] at hh
    exact childV_injective w hh
  · rw [min_eq_left h.le, min_eq_right h'.le] at hl
    rw [max_eq_right h.le, max_eq_left h'.le] at hh
    exact absurd ⟨hl, hh⟩ key
  · rw [min_eq_right h.le, min_eq_left h'.le] at hl
    rw [max_eq_left h.le, max_eq_right h'.le] at hh
    exact absurd ⟨hh, hl⟩ key
  · rw [min_eq_right h.le, min_eq_right h'.le] at hl
    exact childV_injective w hl

/-- Two different spine edges cannot leave the same parent position. -/
theorem spine_child_unique (w : WordIndex r) {j j' : Fin r} (hj : j.succ ∈ w.2.1)
    (hj' : j'.succ ∈ w.2.1) (hp : parV w j = parV w j') : j = j' := by
  have hpp := baseV_injective w hp
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hle := le_parent_of_mem hj (Fin.succ_lt_succ_iff.mpr h)
    rw [← hpp] at hle
    exact absurd (parent_succ_lt w.2.1 j) (not_lt.mpr hle)
  · have hle := le_parent_of_mem hj' (Fin.succ_lt_succ_iff.mpr h)
    rw [hpp] at hle
    exact absurd (parent_succ_lt w.2.1 j') (not_lt.mpr hle)

end MaxCaterpillar.CountCubic
