import MaxCaterpillar.Count.PerUnit
import MaxCaterpillar.Count.TreeForest
import MaxCaterpillar.Audit.CaterpillarTree

/-!
# The class `ω ≤ Δ`

Units with a reduced forest of degree `≤ Δ` satisfy `ω ≤ Δ` (`omegaLe_of_redDeg`): the
caterpillar tree faces (`redDeg_of_isUpCaterpillar`, `Δ = 2`), the faces of the rooted stars
of Brunck et al. (`redDeg_of_isStar`), and the trees of hinge degree `≤ Δ`
(`redDeg_of_hingeDeg_le`).  Units with at most `s` out-leaves at each vertex satisfy
`ω ≤ s + 1` (`omegaLe_of_outLeafBound`).  Every caterpillar function is the face function of
a caterpillar tree with `x_parent - x_leaf` on its leaves (`caterpillarFunction_eq_upTree`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees.TreeFace

open MaxNN CountLower Count
open Classical

variable {N : ℕ} (F : TreeFace N)

/-! ## Tree faces -/

/-- A pair of the description contains `u` iff it is the edge of `u` or of a child of `u`. -/
theorem mem_pair_iff {m : Fin N × Fin N} (hm : m ∈ F.descr.M) (u : Fin N) :
    (m.1 = u ∨ m.2 = u) ↔ ∃ v ∈ F.edgeVerts, F.state v = .hinge ∧
      m = TreeFace.normPair (F.gen v) ∧ (v = u ∨ F.parent v = u) := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
  obtain ⟨hvE, hvs⟩ := mem_filter.mp hv
  constructor
  · intro h
    exact ⟨v, hvE, hvs, rfl, (F.gen_mem v u).mp ((TreeFace.normPair_mem _ u).mp h)⟩
  · rintro ⟨w, hwE, -, he, hw⟩
    have hw' : v = w := F.normPair_inj hvE hwE he
    subst hw'
    exact (TreeFace.normPair_mem _ u).mpr ((F.gen_mem v u).mpr hw)

/-- Hinge neighbours come from hinge edges. -/
theorem dadj_iff {u x : Fin N} : DAdj F.descr u x ↔ ∃ v ∈ F.edgeVerts, F.state v = .hinge ∧
    ((v = u ∧ F.parent v = x) ∨ (v = x ∧ F.parent v = u)) := by
  constructor
  · intro h
    have hm : ∃ m ∈ F.descr.M, (m = (u, x) ∨ m = (x, u)) := by
      rcases h with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    obtain ⟨m, hmM, hmx⟩ := hm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hmM
    obtain ⟨hvE, hvs⟩ := mem_filter.mp hv
    refine ⟨v, hvE, hvs, ?_⟩
    have hp := F.parent_ne_self hvE
    unfold TreeFace.normPair TreeFace.gen at hmx
    split_ifs at hmx <;> simp only [Prod.mk.injEq] at hmx <;>
      rcases hmx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
        | exact Or.inl ⟨h1, h2⟩ | exact Or.inl ⟨h2, h1⟩
        | exact Or.inr ⟨h1, h2⟩ | exact Or.inr ⟨h2, h1⟩
  · rintro ⟨v, hvE, hvs, hv⟩
    have hmM : TreeFace.normPair (F.gen v) ∈ F.descr.M :=
      mem_image.mpr ⟨v, mem_filter.mpr ⟨hvE, hvs⟩, rfl⟩
    unfold DAdj
    unfold TreeFace.normPair TreeFace.gen at hmM
    split_ifs at hmM <;>
      rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact Or.inl hmM | exact Or.inr hmM

/-- A tree leaf with a hinge `σ(x_parent - x_v)` is a pendant. -/
theorem isPend_of_leaf {v : Fin N} (hvE : v ∈ F.edgeVerts)
    (hleaf : ∀ w ∈ F.edgeVerts, F.parent w ≠ v) (hs : F.state v = .hinge) (hup : F.up v = true) :
    IsPend F.descr v := by
  have hgen : F.gen v = (F.parent v, v) := by simp [TreeFace.gen, hup]
  have hpv := F.parent_ne_self hvE
  have hv' := (F.mem_edgeVerts).mp hvE
  -- the only pair at `v` is the edge of `v`
  have honly : ∀ m ∈ F.descr.M, (m.1 = v ∨ m.2 = v) → m = TreeFace.normPair (F.parent v, v) := by
    intro m hm hmv
    obtain ⟨w, hwE, -, rfl, hw⟩ := (mem_pair_iff F hm v).mp hmv
    rcases hw with rfl | hw
    · rw [hgen]
    · exact absurd hw (hleaf w hwE)
  have hmem : TreeFace.normPair (F.parent v, v) ∈ F.descr.M :=
    mem_image.mpr ⟨v, mem_filter.mpr ⟨hvE, hs⟩, by rw [hgen]⟩
  constructor
  · rw [card_eq_one]
    refine ⟨F.parent v, ?_⟩
    ext x
    rw [mem_nbrs, mem_singleton]
    constructor
    · intro hx
      obtain ⟨w, hwE, -, hw⟩ := (dadj_iff F).mp hx
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, hw⟩
      · rfl
      · exact absurd hw (hleaf _ hwE)
    · rintro rfl
      exact (dadj_iff F).mpr ⟨v, hvE, hs, Or.inl ⟨rfl, rfl⟩⟩
  · unfold DKappa
    have hh : F.descr.h v = if v < F.parent v then -1 else 0 := by
      show ((if v = F.root then 1 else 0) - (if v = F.apex then 1 else 0)) +
        ∑ w in F.edgeVerts, (if F.headShift w then
          ((if v = (F.gen w).1 then 1 else 0) - (if v = (F.gen w).2 then 1 else 0)) else 0) = _
      rw [if_neg hv'.1, if_neg hv'.2, sum_eq_single v]
      · have hhs : F.headShift v ↔ v < F.parent v := by
          unfold TreeFace.headShift; rw [hgen, hs]; simp
        rw [hgen]
        simp only [if_neg hpv.symm, if_pos rfl]
        by_cases h : v < F.parent v
        · rw [if_pos (hhs.mpr h), if_pos h]; norm_num
        · rw [if_neg (fun h' => h (hhs.mp h')), if_neg h]; norm_num
      · intro w hwE hwv
        have h1 : v ≠ (F.gen w).1 ∧ v ≠ (F.gen w).2 := by
          constructor <;> intro he
          · have := (F.gen_mem w v).mp (Or.inl he.symm)
            rcases this with h | h
            · exact hwv h
            · exact hleaf w hwE h
          · have := (F.gen_mem w v).mp (Or.inr he.symm)
            rcases this with h | h
            · exact hwv h
            · exact hleaf w hwE h
        simp [h1.1, h1.2]
      · intro h; exact absurd hvE h
    have hc : (F.descr.M.filter fun m => m.1 = v).card = if v < F.parent v then 1 else 0 := by
      by_cases h : v < F.parent v
      · rw [if_pos h, card_eq_one]
        refine ⟨TreeFace.normPair (F.parent v, v), ?_⟩
        ext m
        rw [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hm, hm1⟩; exact honly m hm (Or.inl hm1)
        · rintro rfl
          refine ⟨hmem, ?_⟩
          unfold TreeFace.normPair; rw [if_neg (not_lt.mpr h.le)]
      · rw [if_neg h, card_eq_zero, filter_eq_empty_iff]
        intro m hm hm1
        have := honly m hm (Or.inl hm1)
        rw [this] at hm1
        unfold TreeFace.normPair at hm1
        split_ifs at hm1 with h'
        · exact hpv hm1
        · exact hpv (le_antisymm (not_lt.mp h) (not_lt.mp h'))
    rw [hh, hc]
    split_ifs <;> norm_num

/-- Rooted stars and all their faces have no reduced edge. -/
theorem redDeg_of_isStar (hF : IsStarFace F) (Δ : ℕ) : RedDeg F.descr Δ := by
  intro u
  rw [card_eq_zero.mpr]
  · exact Nat.zero_le _
  rw [filter_eq_empty_iff]
  intro x _ hR
  obtain ⟨v, hvE, hvs, hv⟩ := (dadj_iff F).mp hR.1
  have hleaf : ∀ w ∈ F.edgeVerts, F.parent w ≠ v := by
    intro w hwE h
    rw [(hF w hwE).1] at h
    exact ((F.mem_edgeVerts).mp hvE).1 h.symm
  have hp := isPend_of_leaf F hvE hleaf hvs (hF v hvE).2
  rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hR.2.1 hp
  · exact hR.2.2 hp

/-- Caterpillar trees with upward leaves have reduced degree `≤ 2`. -/
theorem redDeg_of_isUpCaterpillar (hF : IsUpCaterpillar F) : RedDeg F.descr 2 := by
  obtain ⟨P, hrP, haP, hclosed, hinj, hleafP⟩ := hF
  intro u
  set Ch := P.filter fun w => w ≠ F.root ∧ F.parent w = u
  have hCh : Ch.card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    obtain ⟨haP', ha1, ha2⟩ := mem_filter.mp ha
    obtain ⟨hbP', hb1, hb2⟩ := mem_filter.mp hb
    exact hinj a haP' b hbP' ha1 hb1 (ha2.trans hb2.symm)
  have hsub : univ.filter (RAdj F.descr u) ⊆ insert (F.parent u) Ch := by
    intro x hx
    have hR := (mem_filter.mp hx).2
    obtain ⟨v, hvE, hvs, hv⟩ := (dadj_iff F).mp hR.1
    have hv' := (F.mem_edgeVerts).mp hvE
    have hvP : v ∈ P := by
      by_contra hvP
      have hleaf : ∀ w ∈ F.edgeVerts, F.parent w ≠ v := by
        intro w hwE h
        by_cases hwP : w ∈ P
        · exact hvP (h ▸ hclosed w hwP ((F.mem_edgeVerts).mp hwE).1)
        · exact hvP (h ▸ (hleafP w hwP ((F.mem_edgeVerts).mp hwE).2).1)
      have hp := isPend_of_leaf F hvE hleaf hvs (hleafP v hvP hv'.2).2
      rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hR.2.1 hp
      · exact hR.2.2 hp
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, hpu⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hvP, hv'.1, hpu⟩)
  calc (univ.filter (RAdj F.descr u)).card ≤ (insert (F.parent u) Ch).card := card_le_of_subset hsub
    _ ≤ Ch.card + 1 := card_insert_le _ _
    _ ≤ 2 := by omega

/-- Trees of hinge degree `≤ Δ` have reduced degree `≤ Δ`. -/
theorem redDeg_of_hingeDeg_le {Δ : ℕ} (h : ∀ u, F.hingeDeg u ≤ Δ) : RedDeg F.descr Δ := by
  intro u
  refine le_trans ?_ ((F.incid_descr_le u).trans (h u))
  unfold incid
  refine card_le_card_of_inj_on (fun x => ord2 u x) (fun x hx => ?_) (fun x hx x' _ he => ?_)
  · have hR := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨ord2_mem (F.descr_lt) hR.1, ?_⟩
    dsimp only [ord2]; split_ifs <;> simp
  · have hR := (mem_filter.mp hx).2
    have hxu : x ≠ u := fun e => dadj_irrefl F.descr_lt u (by rw [e] at hR; exact hR.1)
    simp only at he
    unfold ord2 at he
    split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> rcases he with ⟨h1, h2⟩ <;>
      first | exact h2 | exact h1 | exact absurd h2 hxu | exact absurd h1 hxu

end MaxCaterpillar.Trees.TreeFace

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees Audit

variable {r : ℕ}

/-- The caterpillar tree of a word has upward leaves. -/
theorem treeFaceOf_isUpCaterpillar (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    TreeFace.IsUpCaterpillar (treeFaceOf w τ) := by
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
    rw [posOf_succ]
    unfold newParent
    rw [if_pos hq]
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
    unfold newParent at he'
    rw [if_pos hp, if_pos hq] at he'
    have := congrArg (Caterpillar.parent S) he'
    rw [parent_nextHead hp hpl, parent_nextHead hq hql] at this
    rw [this]
  · intro v hvP hva
    have hq : posOf w v ∉ insert 0 S := fun h =>
      hvP (Finset.mem_image.2 ⟨_, h, succ_posOf w hva⟩)
    refine ⟨?_, ?_⟩
    · show w.1 (newParent w (posOf w v)).succ ∈ _
      unfold newParent
      rw [if_neg hq]
      exact Finset.mem_image.2 ⟨_, parent_mem_heads _, rfl⟩
    · show decide (posOf w v ∉ insert 0 S) = true
      exact decide_eq_true hq

/-- Every caterpillar function is the face function of a caterpillar tree with upward
leaves. -/
theorem caterpillarFunction_eq_upTree {k : FaceKey r} (hk : k ∈ caterpillarDescriptions r) :
    ∃ F : TreeFace (r + 1 + 1), TreeFace.IsUpCaterpillar F ∧ caterpillarFunction k = F.unit := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hqc
  refine ⟨treeFaceOf w τ, treeFaceOf_isUpCaterpillar w τ, ?_⟩
  unfold caterpillarFunction
  rw [realUnitY_normalizedKey hq]
  funext y
  exact realUnitY_faceKey w τ y

section Class

open Classical

variable {N : ℕ}

/-- `ω(v) ≤ |S|` for any set `S` containing the out-leaf neighbours of `v` and its neighbours
of degree `≥ 2`. -/
theorem trunkDeg_le_card {D : Descr N} {v : Fin N} (S : Finset (Fin N))
    (hO : ∀ u, DAdj D v u → IsOLeaf D u → u ∈ S)
    (hW : ∀ w, DAdj D v w → 1 < (nbrs D w).card → w ∈ S) : trunkDeg D v ≤ S.card := by
  unfold trunkDeg
  set O := univ.filter fun u => DAdj D v u ∧ IsOLeaf D u
  have hOS : O ⊆ S := fun u hu => hO u (mem_filter.mp hu).2.1 (mem_filter.mp hu).2.2
  split_ifs with h
  · obtain ⟨w, hw1, hw2⟩ := h
    have hwO : w ∉ O := fun hw => by
      have := (mem_filter.mp hw).2.2.1; omega
    have := card_le_of_subset (insert_subset_iff.mpr ⟨hW w hw1 hw2, hOS⟩)
    rw [card_insert_of_not_mem hwO] at this
    exact this
  · simpa using card_le_of_subset hOS

/-- A reduced forest of degree `≤ Δ` gives `ω ≤ Δ`. -/
theorem omegaLe_of_redDeg {D : Descr N} {Δ : ℕ} (hΔ : 1 ≤ Δ) (h : RedDeg D Δ) :
    OmegaLe D Δ := by
  intro v
  by_cases hv : IsPend D v
  · refine (trunkDeg_le_card (nbrs D v) (fun u hu _ => mem_nbrs.mpr hu)
      (fun w hw _ => mem_nbrs.mpr hw)).trans ?_
    rw [hv.1]; exact hΔ
  · refine (trunkDeg_le_card (univ.filter (RAdj D v)) (fun u hu ho => ?_) (fun w hw hw2 => ?_)).trans
      (h v)
    · exact mem_filter.mpr ⟨mem_univ _, hu, hv, not_pend_of_oleaf ho⟩
    · exact mem_filter.mpr ⟨mem_univ _, hw, hv, fun hp => by rw [hp.1] at hw2; omega⟩

/-- Under `i < j`, the pairs at `u` correspond to the neighbours of `u`. -/
theorem card_incid_le_nbrs {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) (u : Fin N) :
    (incid D.M u).card ≤ (nbrs D u).card := by
  have hf : ∀ m ∈ incid D.M u, m = (u, if m.1 = u then m.2 else m.1) ∨
      m = (if m.1 = u then m.2 else m.1, u) := by
    rintro ⟨a, b⟩ hm
    rcases (mem_filter.mp hm).2 with h | h <;> simp only at h
    · subst h; simp
    · subst h
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab]
  refine card_le_card_of_inj_on (fun m => if m.1 = u then m.2 else m.1) (fun m hm => ?_)
    (fun m hm m' hm' he => ?_)
  · have hmM := (mem_filter.mp hm).1
    rw [mem_nbrs]
    rcases hf m hm with e | e
    · left; rw [← e]; exact hmM
    · right; rw [← e]; exact hmM
  · have h1 := hlt m (mem_filter.mp hm).1
    have h2 := hlt m' (mem_filter.mp hm').1
    simp only at he
    rcases hf m hm with e | e <;> rcases hf m' hm' with e' | e'
    · rw [e, e', he]
    · rw [e] at h1; rw [e', ← he] at h2; exact absurd (h1.trans h2) (lt_irrefl _)
    · rw [e] at h1; rw [e', ← he] at h2; exact absurd (h1.trans h2) (lt_irrefl _)
    · rw [e, e', he]

/-- At most `s` out-leaves at every vertex gives `ω ≤ s + 1`. -/
theorem omegaLe_of_outLeafBound {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) {s : ℕ}
    (h : OutLeafBound D s) : OmegaLe D (s + 1) := by
  intro v
  unfold trunkDeg
  have hO : (univ.filter fun u => DAdj D v u ∧ IsOLeaf D u).card ≤ s := by
    refine h v _ fun u hu => ⟨(mem_filter.mp hu).2.1, ?_, (mem_filter.mp hu).2.2.2⟩
    have h1 := (mem_filter.mp hu).2.2.1
    have hle := card_incid_le_nbrs hlt u
    have hpos : 0 < (incid D.M u).card := by
      obtain ⟨x, hx⟩ := card_pos.mp (by rw [h1]; exact Nat.one_pos : 0 < (nbrs D u).card)
      rcases mem_nbrs.mp hx with hx | hx
      · exact card_pos.mpr ⟨_, mem_filter.mpr ⟨hx, Or.inl rfl⟩⟩
      · exact card_pos.mpr ⟨_, mem_filter.mpr ⟨hx, Or.inr rfl⟩⟩
    rw [h1] at hle
    exact le_antisymm hle hpos
  split_ifs
  · exact Nat.add_le_add_right hO 1
  · exact (Nat.add_le_add_right hO 0).trans (Nat.le_succ _)

end Class

end MaxCaterpillar.Count
