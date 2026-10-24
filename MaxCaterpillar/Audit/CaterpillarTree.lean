import MaxCaterpillar.Trees
import MaxCaterpillar.Audit.Expansion

/-! # Faithfulness: every caterpillar function is the face function of a caterpillar tree

`caterpillarFunction k` is defined as `realUnitY k`, a paramid unit in reduced simplex
coordinates, for normalized keys `k ∈ caterpillarDescriptions r`. This file proves the
announced form directly in the input coordinates: for every `k ∈ 𝒦₀` there is a tree face
`F` (`Trees/Quadratic.lean`) whose tree is a caterpillar (`TreeFace.IsCaterpillar`) and

`caterpillarFunction k x = σ(x_root − x_apex + Σ_{v ≠ apex, root} edgeTerm_v(x))`,

where every edge `{v, parent v}` of the tree contributes `0` (omitted), the difference
`x_i − x_j` of its endpoints (linear) or `σ(x_i − x_j)` (hinge). The head is therefore the
difference `x_root − x_apex` plus the linear edge differences; after normalization of the
key, a hinge `σ(x_i − x_j)` with `i > j` is stored as `x_i − x_j + σ(x_j − x_i)`, so the
stored head `k.1` is a sum of such differences, but the function is the one displayed.

The tree is the caterpillar of the word: the spine is the set of block heads, ordered along
the word, rooted at the last head (the head vertex `x_root`), and every other vertex is a
leaf attached to the spine. As a corollary, `IsTreeExpansion` is satisfiable
(`exists_isTreeExpansion`).
-/

open BigOperators Finset

namespace MaxCaterpillar

namespace Trees.TreeFace

variable {N : ℕ}

/-- The tree of `F` (on all vertices except the apex, rooted at `F.root` by `F.parent`) is a
*caterpillar whose spine starts at the root*: there is a spine `P` containing the root and
not the apex, closed under `parent`, in which no two vertices other than the root share a
parent (so `P` is a path starting at the root), and every vertex outside `P` other than the
apex is attached to the spine (`parent v ∈ P`); such a vertex is a leaf
(`IsCaterpillar.not_parent_of_not_mem`). -/
def IsCaterpillar (F : TreeFace N) : Prop :=
  ∃ P : Finset (Fin N), F.root ∈ P ∧ F.apex ∉ P ∧
    (∀ v ∈ P, v ≠ F.root → F.parent v ∈ P) ∧
    (∀ u ∈ P, ∀ v ∈ P, u ≠ F.root → v ≠ F.root → F.parent u = F.parent v → u = v) ∧
    (∀ v, v ∉ P → v ≠ F.apex → F.parent v ∈ P)

/-- In a caterpillar, the vertices off the spine are leaves: no vertex has them as parent. -/
theorem IsCaterpillar.not_parent_of_not_mem {F : TreeFace N} {P : Finset (Fin N)}
    (hP : F.root ∈ P ∧ F.apex ∉ P ∧
      (∀ v ∈ P, v ≠ F.root → F.parent v ∈ P) ∧
      (∀ u ∈ P, ∀ v ∈ P, u ≠ F.root → v ≠ F.root → F.parent u = F.parent v → u = v) ∧
      (∀ v, v ∉ P → v ≠ F.apex → F.parent v ∈ P))
    {v : Fin N} (hv : v ∉ P) {w : Fin N} (hw : w ∈ F.edgeVerts) : F.parent w ≠ v := by
  obtain ⟨-, -, hclosed, -, hleaf⟩ := hP
  have hw' := F.mem_edgeVerts.mp hw
  intro he
  by_cases hwP : w ∈ P
  · exact hv (he ▸ hclosed w hwP hw'.1)
  · exact hv (he ▸ hleaf w hwP hw'.2)

end Trees.TreeFace

namespace Audit

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.Width ParamidGeom
open Trees

variable {r : ℕ}

/-! ## The spine of an ordered caterpillar -/

section Spine

variable (S : Finset (Fin (r + 1)))

/-- The next block head after position `q` (the spine successor of a head). -/
noncomputable def nextHead (q : Fin (r + 1)) : Fin (r + 1) :=
  if h : (S.filter (q < ·)).Nonempty then (S.filter (q < ·)).min' h else q

variable {S}

theorem parent_mem_heads (q : Fin (r + 1)) : Caterpillar.parent S q ∈ insert 0 S := by
  have h := Finset.max'_mem (insert 0 (S.filter fun i => i < q)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 h with h | h
  · exact Finset.mem_insert.2 (Or.inl h)
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.1 h).1

theorem lastHead_mem_heads : lastHead S ∈ insert 0 S :=
  Finset.max'_mem _ _

theorem le_lastHead {q : Fin (r + 1)} (hq : q ∈ insert 0 S) : q ≤ lastHead S :=
  Finset.le_max' _ _ hq

theorem nextHead_spec {q : Fin (r + 1)} (hq : q ∈ insert 0 S) (hql : q ≠ lastHead S) :
    nextHead S q ∈ S ∧ q < nextHead S q ∧ ∀ s ∈ S, q < s → nextHead S q ≤ s := by
  have hlt : q < lastHead S := lt_of_le_of_ne (le_lastHead hq) hql
  have hlS : lastHead S ∈ S := by
    rcases Finset.mem_insert.1 (lastHead_mem_heads (S := S)) with h | h
    · rw [h] at hlt; exact absurd hlt (Fin.not_lt_zero _)
    · exact h
  have hne : (S.filter (q < ·)).Nonempty := ⟨_, Finset.mem_filter.2 ⟨hlS, hlt⟩⟩
  have hmem := Finset.min'_mem _ hne
  unfold nextHead
  rw [dif_pos hne]
  exact ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2,
    fun s hs hqs => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hs, hqs⟩)⟩

theorem parent_nextHead {q : Fin (r + 1)} (hq : q ∈ insert 0 S) (hql : q ≠ lastHead S) :
    Caterpillar.parent S (nextHead S q) = q := by
  obtain ⟨-, hlt, hmin⟩ := nextHead_spec hq hql
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; exact Fin.zero_le _
    · obtain ⟨hyS, hyn⟩ := Finset.mem_filter.1 h
      by_contra hqy
      exact absurd (hmin y hyS (lt_of_not_le hqy)) (not_le.2 hyn)
  · apply Finset.le_max'
    rcases Finset.mem_insert.1 hq with h | h
    · exact Finset.mem_insert.2 (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨h, hlt⟩)

theorem nextHead_parent (h0 : (0 : Fin (r + 1)) ∉ S) {q : Fin (r + 1)} (hq : q ∈ S) :
    nextHead S (Caterpillar.parent S q) = q := by
  have hq0 : 0 < q := by
    exact Fin.pos_iff_ne_zero.2 (fun h => h0 (h ▸ hq))
  have hp := parent_lt (S := S) hq0
  have hne : (S.filter (Caterpillar.parent S q < ·)).Nonempty :=
    ⟨q, Finset.mem_filter.2 ⟨hq, hp⟩⟩
  unfold nextHead
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hq, hp⟩)
  · apply Finset.le_min'
    intro s hs
    obtain ⟨hsS, hps⟩ := Finset.mem_filter.1 hs
    by_contra hsq
    have hsq' : s < q := lt_of_not_le hsq
    have hmem : s ∈ insert 0 (S.filter fun i => i < q) :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hsS, hsq'⟩)
    have hle : s ≤ Caterpillar.parent S q :=
      Finset.le_max' (insert 0 (S.filter fun i => i < q)) s hmem
    exact absurd hps (not_lt.2 hle)

theorem lastHead_ne_of_mem (h0 : (0 : Fin (r + 1)) ∉ S) {q : Fin (r + 1)} (hq : q ∈ S) :
    Caterpillar.parent S q ≠ lastHead S := by
  have hq0 : 0 < q := Fin.pos_iff_ne_zero.2 (fun h => h0 (h ▸ hq))
  have hp := parent_lt (S := S) hq0
  exact ne_of_lt (lt_of_lt_of_le hp (le_lastHead (Finset.mem_insert_of_mem hq)))

end Spine

/-! ## The caterpillar tree face of a word and a face -/

/-- The three states of a face label. -/
def toState (t : Fin 3) : EdgeState :=
  if t = 1 then .linear else if t = 2 then .hinge else .omit

/-- The contribution of an edge in a given state. -/
noncomputable def termOf : EdgeState → ℝ → ℝ
  | .omit, _ => 0
  | .linear, t => t
  | .hinge, t => MaxNN.relu t

theorem edgeTerm_eq {N : ℕ} (F : TreeFace N) (v : Fin N) (y : Fin N → ℝ) :
    F.edgeTerm v y = termOf (F.state v) (y (F.gen v).1 - y (F.gen v).2) := by
  unfold TreeFace.edgeTerm
  cases F.state v <;> rfl

section Word

variable (w : WordIndex r) (τ : (wordLabels w) → Fin 3)

/-- The position in the word of a non-apex vertex. -/
noncomputable def posOf (u : Fin (r + 1 + 1)) : Fin (r + 1) :=
  if h : w.1.symm u = 0 then lastHead w.2.1 else (w.1.symm u).pred h

theorem posOf_succ (q : Fin (r + 1)) : posOf w (w.1 q.succ) = q := by
  unfold posOf
  rw [Equiv.symm_apply_apply, dif_neg (Fin.succ_ne_zero q), Fin.pred_succ]

theorem succ_posOf {u : Fin (r + 1 + 1)} (hu : u ≠ w.1 0) : w.1 (posOf w u).succ = u := by
  have h : w.1.symm u ≠ 0 := fun h => hu (by rw [← h, Equiv.apply_symm_apply])
  unfold posOf
  rw [dif_neg h, Fin.succ_pred, Equiv.apply_symm_apply]

/-- The parent position after re-rooting the caterpillar at its last head: a head moves to
the next head, a leaf keeps its head. -/
noncomputable def newParent (q : Fin (r + 1)) : Fin (r + 1) :=
  by classical exact if q ∈ insert 0 w.2.1 then nextHead w.2.1 q else Caterpillar.parent w.2.1 q

/-- A depth for the re-rooted tree. -/
noncomputable def newDepth (q : Fin (r + 1)) : ℕ :=
  by classical exact if q ∈ insert 0 w.2.1 then 2 * (w.2.1.filter (q < ·)).card
    else 2 * (w.2.1.filter (Caterpillar.parent w.2.1 q < ·)).card + 1

/-- The label position of the tree edge at position `q`. -/
noncomputable def edgeLabel (q : Fin (r + 1)) : Fin (r + 1) :=
  by classical exact if q ∈ insert 0 w.2.1 then nextHead w.2.1 q else q

theorem edgeLabel_of_mem {q : Fin (r + 1)} (h : q ∈ insert 0 w.2.1) :
    edgeLabel w q = nextHead w.2.1 q := by
  unfold edgeLabel; exact if_pos h

theorem edgeLabel_of_not_mem {q : Fin (r + 1)} (h : q ∉ insert 0 w.2.1) :
    edgeLabel w q = q := by
  unfold edgeLabel; exact if_neg h

theorem newParent_of_mem {q : Fin (r + 1)} (h : q ∈ insert 0 w.2.1) :
    newParent w q = nextHead w.2.1 q := by
  unfold newParent; exact if_pos h

theorem newParent_of_not_mem {q : Fin (r + 1)} (h : q ∉ insert 0 w.2.1) :
    newParent w q = Caterpillar.parent w.2.1 q := by
  unfold newParent; exact if_neg h

theorem newDepth_of_mem {q : Fin (r + 1)} (h : q ∈ insert 0 w.2.1) :
    newDepth w q = 2 * (w.2.1.filter (q < ·)).card := by
  unfold newDepth; convert if_pos h

theorem newDepth_of_not_mem {q : Fin (r + 1)} (h : q ∉ insert 0 w.2.1) :
    newDepth w q = 2 * (w.2.1.filter (Caterpillar.parent w.2.1 q < ·)).card + 1 := by
  unfold newDepth; convert if_neg h

/-- The state of the label at position `q > 0` given by the face `τ`. -/
noncomputable def labelState (q : Fin (r + 1)) : EdgeState :=
  if h : q = 0 then .omit else
    toState (keyExt (wordLabels w) τ (edgeVecs (wordBase w) w.2.1 (q.pred h)))

theorem zero_not_mem_cuts : (0 : Fin (r + 1)) ∉ w.2.1 := by
  intro h
  have h1 := (Finset.mem_erase.1 w.2.2).2
  have h2 := Finset.mem_powerset.1 h1 h
  exact (Finset.mem_erase.1 h2).1 rfl

/-- The caterpillar tree face of the word `w` and the face `τ`. -/
noncomputable def treeFaceOf : TreeFace (r + 1 + 1) where
  apex := w.1 0
  root := w.1 (lastHead w.2.1).succ
  parent := fun u => w.1 (newParent w (posOf w u)).succ
  depth := fun u => newDepth w (posOf w u)
  up := fun u => by classical exact decide (posOf w u ∉ insert 0 w.2.1)
  state := fun u => labelState w τ (edgeLabel w (posOf w u))
  root_ne_apex := fun h => Fin.succ_ne_zero _ (w.1.injective h)
  parent_ne_apex := fun _ _ _ h => Fin.succ_ne_zero _ (w.1.injective h)
  depth_lt := by
    classical
    intro u hua hur
    have hq : posOf w u ≠ lastHead w.2.1 := fun h => hur (by rw [← h, succ_posOf w hua])
    show newDepth w (posOf w (w.1 (newParent w (posOf w u)).succ)) < newDepth w (posOf w u)
    rw [posOf_succ]
    set q := posOf w u
    set S := w.2.1
    by_cases hH : q ∈ insert 0 S
    · obtain ⟨hnS, hlt, -⟩ := nextHead_spec hH hq
      rw [newParent_of_mem w hH, newDepth_of_mem w (Finset.mem_insert_of_mem hnS),
        newDepth_of_mem w hH]
      have hss : S.filter (nextHead S q < ·) ⊂ S.filter (q < ·) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨nextHead S q, Finset.mem_filter.2 ⟨hnS, hlt⟩,
            fun h => lt_irrefl _ (Finset.mem_filter.1 h).2⟩
        · intro s hs
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hs
          exact Finset.mem_filter.2 ⟨h1, lt_trans hlt h2⟩
      have hc := Finset.card_lt_card hss
      first
        | exact Nat.mul_lt_mul_of_pos_left hc (by norm_num)
        | exact (Nat.mul_lt_mul_left (by norm_num)).2 hc
        | exact Nat.mul_lt_mul_of_lt_of_le (le_refl 2) hc (by norm_num)
    · rw [newParent_of_not_mem w hH, newDepth_of_mem w (parent_mem_heads q),
        newDepth_of_not_mem w hH]
      exact Nat.lt_succ_self _

/-- The tree face of a word is a caterpillar: the spine is the set of block heads. -/
theorem treeFaceOf_isCaterpillar : (treeFaceOf w τ).IsCaterpillar := by
  classical
  set S := w.2.1
  refine ⟨(insert 0 S).image fun q => w.1 q.succ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨_, lastHead_mem_heads, rfl⟩
  · intro h
    obtain ⟨q, -, hq⟩ := Finset.mem_image.1 h
    exact Fin.succ_ne_zero _ (w.1.injective hq)
  · intro v hv hvr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
    have hql : q ≠ lastHead S := fun h => hvr (by rw [h]; rfl)
    show w.1 (newParent w (posOf w (w.1 q.succ))).succ ∈ _
    rw [posOf_succ, newParent_of_mem w hq]
    exact Finset.mem_image.2 ⟨_, Finset.mem_insert_of_mem (nextHead_spec hq hql).1, rfl⟩
  · intro u hu v hv hur hvr he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
    have hpl : p ≠ lastHead S := fun h => hur (by rw [h]; rfl)
    have hql : q ≠ lastHead S := fun h => hvr (by rw [h]; rfl)
    change w.1 (newParent w (posOf w (w.1 p.succ))).succ =
      w.1 (newParent w (posOf w (w.1 q.succ))).succ at he
    rw [posOf_succ, posOf_succ] at he
    have he' := Fin.succ_injective _ (w.1.injective he)
    rw [newParent_of_mem w hp, newParent_of_mem w hq] at he'
    have := congrArg (Caterpillar.parent S) he'
    rw [parent_nextHead hp hpl, parent_nextHead hq hql] at this
    rw [this]
  · intro v hvP hva
    show w.1 (newParent w (posOf w v)).succ ∈ _
    have hq : posOf w v ∉ insert 0 S := fun h =>
      hvP (Finset.mem_image.2 ⟨_, h, succ_posOf w hva⟩)
    rw [newParent_of_not_mem w hq]
    exact Finset.mem_image.2 ⟨_, parent_mem_heads _, rfl⟩

/-- The edge contribution of the label at position `q'`. -/
noncomputable def labelTerm (q' : Fin (r + 1)) (y : Fin (r + 1 + 1) → ℝ) : ℝ :=
  termOf (labelState w τ q') (y (w.1 (Caterpillar.parent w.2.1 q').succ) - y (w.1 q'.succ))

theorem treeFaceOf_edgeTerm {q : Fin (r + 1)} (hq : q ≠ lastHead w.2.1)
    (y : Fin (r + 1 + 1) → ℝ) :
    (treeFaceOf w τ).edgeTerm (w.1 q.succ) y = labelTerm w τ (edgeLabel w q) y := by
  classical
  rw [edgeTerm_eq]
  unfold labelTerm
  show termOf (labelState w τ (edgeLabel w (posOf w (w.1 q.succ)))) _ = _
  rw [posOf_succ]
  congr 1
  unfold TreeFace.gen
  show (y (if decide (posOf w (w.1 q.succ) ∉ insert 0 w.2.1) = true
      then (w.1 (newParent w (posOf w (w.1 q.succ))).succ, w.1 q.succ)
      else (w.1 q.succ, w.1 (newParent w (posOf w (w.1 q.succ))).succ)).1 -
    y (if decide (posOf w (w.1 q.succ) ∉ insert 0 w.2.1) = true
      then (w.1 (newParent w (posOf w (w.1 q.succ))).succ, w.1 q.succ)
      else (w.1 q.succ, w.1 (newParent w (posOf w (w.1 q.succ))).succ)).2) = _
  rw [posOf_succ]
  unfold newParent edgeLabel
  by_cases hH : q ∈ insert 0 w.2.1
  · simp only [hH, not_true_eq_false, decide_False, if_false, if_true]
    rw [parent_nextHead hH hq]
  · simp only [hH, not_false_eq_true, decide_True, if_true, if_false]

/-- The edge sum of the tree face is the sum over all labels. -/
theorem treeFaceOf_sum (y : Fin (r + 1 + 1) → ℝ) :
    ∑ v in (treeFaceOf w τ).edgeVerts, (treeFaceOf w τ).edgeTerm v y =
      ∑ j : Fin r, labelTerm w τ j.succ y := by
  classical
  set S := w.2.1
  have h0 : (0 : Fin (r + 1)) ∉ S := zero_not_mem_cuts w
  have hev : ∀ v, v ∈ (treeFaceOf w τ).edgeVerts ↔ v ≠ w.1 (lastHead S).succ ∧ v ≠ w.1 0 :=
    fun v => (treeFaceOf w τ).mem_edgeVerts
  -- vertices to positions
  have h1 : ∑ v in (treeFaceOf w τ).edgeVerts, (treeFaceOf w τ).edgeTerm v y =
      ∑ q in univ.erase (lastHead S), labelTerm w τ (edgeLabel w q) y := by
    refine Finset.sum_bij' (fun v _ => posOf w v) (fun v hv => ?_) (fun v hv => ?_)
      (fun q _ => w.1 q.succ) (fun q hq => ?_) (fun v hv => ?_) (fun q _ => posOf_succ w q)
    · have hv' := (hev v).1 hv
      refine Finset.mem_erase.2 ⟨fun h => hv'.1 ?_, Finset.mem_univ _⟩
      rw [← h, succ_posOf w hv'.2]
    · have hv' := (hev v).1 hv
      have hq : posOf w v ≠ lastHead S := fun h => hv'.1 (by rw [← h, succ_posOf w hv'.2])
      conv_lhs => rw [← succ_posOf w hv'.2]
      exact treeFaceOf_edgeTerm w τ hq y
    · have hq' := (Finset.mem_erase.1 hq).1
      refine (hev _).2 ⟨fun h => hq' (Fin.succ_injective _ (w.1.injective h)),
        fun h => Fin.succ_ne_zero _ (w.1.injective h)⟩
    · exact succ_posOf w ((hev v).1 hv).2
  -- positions to labels
  have h2 : ∑ q in univ.erase (lastHead S), labelTerm w τ (edgeLabel w q) y =
      ∑ q' in univ.erase 0, labelTerm w τ q' y := by
    refine Finset.sum_bij' (fun q _ => edgeLabel w q) (fun q hq => ?_) (fun q _ => rfl)
      (fun q' _ => if q' ∈ S then Caterpillar.parent S q' else q') (fun q' hq' => ?_)
      (fun q hq => ?_) (fun q' hq' => ?_)
    · have hql := (Finset.mem_erase.1 hq).1
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      show edgeLabel w q ≠ 0
      by_cases hH : q ∈ insert 0 S
      · rw [edgeLabel_of_mem w hH]
        intro h; exact h0 (h ▸ (nextHead_spec hH hql).1)
      · rw [edgeLabel_of_not_mem w hH]
        intro h; exact hH (h ▸ Finset.mem_insert_self 0 S)
    · have hq0 := (Finset.mem_erase.1 hq').1
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      dsimp only
      by_cases hS : q' ∈ S
      · rw [if_pos hS]; exact lastHead_ne_of_mem h0 hS
      · rw [if_neg hS]
        intro h
        have hl := lastHead_mem_heads (S := S)
        rw [← h] at hl
        rcases Finset.mem_insert.1 hl with h' | h'
        · exact hq0 h'
        · exact hS h'
    · have hql := (Finset.mem_erase.1 hq).1
      dsimp only
      by_cases hH : q ∈ insert 0 S
      · rw [edgeLabel_of_mem w hH, if_pos (nextHead_spec hH hql).1, parent_nextHead hH hql]
      · rw [edgeLabel_of_not_mem w hH, if_neg (fun h => hH (Finset.mem_insert_of_mem h))]
    · have hq0 := (Finset.mem_erase.1 hq').1
      dsimp only
      by_cases hS : q' ∈ S
      · rw [if_pos hS, edgeLabel_of_mem w (parent_mem_heads q'), nextHead_parent h0 hS]
      · have hH : q' ∉ insert 0 S := by
          intro h
          rcases Finset.mem_insert.1 h with h | h
          · exact hq0 h
          · exact hS h
        rw [if_neg hS, edgeLabel_of_not_mem w hH]
  -- labels to `Fin r`
  have h3 : ∑ q' in univ.erase 0, labelTerm w τ q' y = ∑ j : Fin r, labelTerm w τ j.succ y := by
    have := Finset.add_sum_erase (univ : Finset (Fin (r + 1))) (fun q' => labelTerm w τ q' y)
      (Finset.mem_univ 0)
    rw [Fin.sum_univ_succ] at this
    linarith
  rw [h1, h2, h3]

theorem dot_sum_left {m : ℕ} (V : Finset (Fin m → ℝ)) (Y : Fin m → ℝ) :
    dot (∑ v in V, v) Y = ∑ v in V, dot v Y := by
  simp only [dot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- The face key of `τ` has the tree face function of `treeFaceOf w τ`. -/
theorem realUnitY_faceKey (y : Fin (r + 1 + 1) → ℝ) :
    realUnitY (faceKey (wordGamma w) (wordLabels w) τ) y = (treeFaceOf w τ).unit y := by
  classical
  set Y := (CoordAux.coordT (r + 1)).mulVec y
  have hvtx : ∀ c : Fin (r + 1 + 1), dot (toR (ParamidChain.vtx c)) Y = y c - y 0 :=
    fun c => dot_toR_vtx_coordT (r + 1) c y
  -- the labels
  have hinj : Function.Injective (edgeVecs (wordBase w) w.2.1) :=
    edgeVecs_simplex_injective (fun i => w.1 i.succ)
      (w.1.injective.comp (Fin.succ_injective (r + 1))) w.2.1
  have hlab : ∀ j : Fin r, dot (edgeVecs (wordBase w) w.2.1 j) Y =
      y (w.1 (Caterpillar.parent w.2.1 j.succ).succ) - y (w.1 j.succ.succ) := by
    intro j
    simp only [edgeVecs, wordBase]
    rw [SupportCut.dot_sub_left, hvtx, hvtx]
    ring
  have hterm : ∀ v : Fin (r + 1) → ℝ,
      ((if keyExt (wordLabels w) τ v = 1 then dot v Y else 0) + (if keyExt (wordLabels w) τ v = 2 then MaxNN.relu (dot v Y) else 0)) =
        termOf (toState (keyExt (wordLabels w) τ v)) (dot v Y) := by
    intro v
    unfold toState
    by_cases h1 : keyExt (wordLabels w) τ v = 1
    · rw [if_pos h1, if_pos h1, if_neg (by rw [h1]; decide)]; simp [termOf]
    · by_cases h2 : keyExt (wordLabels w) τ v = 2
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]; simp [termOf]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; simp [termOf]
  have hsum : ∑ v in (wordLabels w).filter (fun v => keyExt (wordLabels w) τ v = 1), dot v Y +
      ∑ v in (wordLabels w).filter (fun v => keyExt (wordLabels w) τ v = 2), MaxNN.relu (dot v Y) =
      ∑ j : Fin r, labelTerm w τ j.succ y := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    show ∑ v in Finset.univ.image (edgeVecs (wordBase w) w.2.1), _ = _
    rw [Finset.sum_image fun a _ b _ h => hinj h]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold labelTerm labelState
    rw [dif_neg (Fin.succ_ne_zero j), Fin.pred_succ, hlab]
  have hgamma : dot (wordGamma w) Y = y (w.1 (lastHead w.2.1).succ) - y (w.1 0) := by
    simp only [wordGamma, wordBase, wordApex]
    rw [SupportCut.dot_sub_left, hvtx, hvtx]
    ring
  unfold realUnitY paramidOn faceKey TreeFace.unit
  simp only
  rw [SupportCut.dot_add_left, dot_sum_left, treeFaceOf_sum]
  show MaxNN.relu (dot (wordGamma w) Y + ∑ v in (wordLabels w).filter (fun v => keyExt (wordLabels w) τ v = 1), dot v Y +
      ∑ v in (wordLabels w).filter (fun v => keyExt (wordLabels w) τ v = 2), MaxNN.relu (dot v Y)) = _
  rw [add_assoc, hsum, hgamma]
  rfl

end Word

/-- **Faithfulness of the dictionary.** Every caterpillar function is the face function of a
caterpillar tree face: for `k ∈ 𝒦₀` there is `F` with `F.IsCaterpillar` and
`caterpillarFunction k x = σ(x_root − x_apex + Σ_v edgeTerm_v(x))` for all `x`. -/
theorem caterpillarFunction_eq_treeFace (r : ℕ) {k : FaceKey r}
    (hk : k ∈ caterpillarDescriptions r) :
    ∃ F : TreeFace (r + 1 + 1), F.IsCaterpillar ∧ caterpillarFunction k = F.unit := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hqc
  refine ⟨treeFaceOf w τ, treeFaceOf_isCaterpillar w τ, ?_⟩
  unfold caterpillarFunction
  rw [realUnitY_normalizedKey hq]
  funext y
  exact realUnitY_faceKey w τ y

/-- The same statement, unfolded: the caterpillar function evaluated at `x`. -/
theorem caterpillarFunction_eq_tree (r : ℕ) {k : FaceKey r}
    (hk : k ∈ caterpillarDescriptions r) :
    ∃ F : TreeFace (r + 1 + 1), F.IsCaterpillar ∧ ∀ x : Point (r + 1 + 1),
      caterpillarFunction k x =
        MaxNN.relu (x F.root - x F.apex + ∑ v in F.edgeVerts, F.edgeTerm v x) := by
  obtain ⟨F, hF, he⟩ := caterpillarFunction_eq_treeFace r hk
  exact ⟨F, hF, fun x => by rw [he]; rfl⟩

/-! ## Nonvacuity of the tree, rooted-star and mixed expansions -/

/-- A caterpillar expansion is an expansion by caterpillar tree faces. -/
theorem isTreeExpansion_of_isCaterpillarExpansion (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    ∃ K' : Finset (TreeFace (r + 1 + 1)), (∀ F ∈ K', F.IsCaterpillar) ∧
      K'.card ≤ K.card ∧ IsTreeExpansion r K' := by
  classical
  obtain ⟨hsub, d, a, h⟩ := hK
  have hT : ∀ k : K, ∃ F : TreeFace (r + 1 + 1), F.IsCaterpillar ∧
      caterpillarFunction k.1 = F.unit := fun k => caterpillarFunction_eq_treeFace r (hsub k.2)
  choose T hTc hTu using hT
  refine ⟨K.attach.image T, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hF
    exact hTc k
  · exact Finset.card_image_le.trans (Finset.card_attach).le
  · refine ⟨fun F => ∑ k in K.attach.filter (fun k => T k = F), d k.1, a, fun x => ?_⟩
    rw [h x]
    congr 1
    simp only [Finset.sum_mul]
    rw [show ∑ k in K, d k * caterpillarFunction k x =
        ∑ k in K.attach, d k.1 * caterpillarFunction k.1 x from Finset.sum_attach.symm]
    symm
    calc ∑ F in K.attach.image T, ∑ k in K.attach.filter (fun k => T k = F), d k.1 * F.unit x
        = ∑ F in K.attach.image T, ∑ k in K.attach.filter (fun k => T k = F),
            d k.1 * caterpillarFunction k.1 x := by
          refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun k hk => ?_
          rw [← (Finset.mem_filter.1 hk).2, hTu k]
      _ = ∑ k in K.attach, d k.1 * caterpillarFunction k.1 x :=
          Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem T hk) _

/-- **Nonvacuity of the tree lower bounds.** For every `N = r + 2` the maximum has an
expansion by tree face functions, all of whose trees are caterpillars. -/
theorem exists_isTreeExpansion (r : ℕ) :
    ∃ K : Finset (TreeFace (r + 1 + 1)), (∀ F ∈ K, F.IsCaterpillar) ∧ IsTreeExpansion r K := by
  obtain ⟨K, hK⟩ := exists_isCaterpillarExpansion r
  obtain ⟨K', h1, -, h2⟩ := isTreeExpansion_of_isCaterpillarExpansion r hK
  exact ⟨K', h1, h2⟩

/-- **Nonvacuity of the rooted-star lower bounds.** Every caterpillar expansion is a
rooted-star expansion (all rooted-star coefficients zero). -/
theorem isRootedStarExpansion_of_isCaterpillarExpansion (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) : IsRootedStarExpansion r K := by
  obtain ⟨hsub, d, a, h⟩ := hK
  refine ⟨hsub, d, fun _ => 0, a, fun x => ?_⟩
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  exact h x

theorem exists_isRootedStarExpansion (r : ℕ) : ∃ K, IsRootedStarExpansion r K := by
  obtain ⟨K, hK⟩ := exists_isCaterpillarExpansion r
  exact ⟨K, isRootedStarExpansion_of_isCaterpillarExpansion r hK⟩

/-- **Nonvacuity of the mixed lower bound.** Every caterpillar expansion is a mixed expansion
with no tree units (`K₂ = ∅`, so the `HubOK` hypothesis holds vacuously). -/
theorem isMixedExpansion_of_isCaterpillarExpansion (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) : IsMixedExpansion r K ∅ := by
  obtain ⟨hsub, d, a, h⟩ := hK
  refine ⟨hsub, d, fun _ => 0, a, fun x => ?_⟩
  rw [Finset.sum_empty, add_zero]
  exact h x

theorem exists_isMixedExpansion (r : ℕ) :
    ∃ (K₁ : Finset (FaceKey r)) (K₂ : Finset (TreeFace (r + 1 + 1))),
      IsMixedExpansion r K₁ K₂ ∧ ∀ Δ, ∀ F ∈ K₂, HubOK F.descr Δ := by
  obtain ⟨K, hK⟩ := exists_isCaterpillarExpansion r
  exact ⟨K, ∅, isMixedExpansion_of_isCaterpillarExpansion r hK, fun _ _ h => absurd h
    (Finset.not_mem_empty _)⟩

end Audit
end MaxCaterpillar
