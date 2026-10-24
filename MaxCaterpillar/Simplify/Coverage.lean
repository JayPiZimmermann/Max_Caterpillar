import MaxCaterpillar.Trees.Combined
import Mathlib.Combinatorics.DoubleCounting

/-!
# Coverage: a per-unit count for every hinge forest with few out-leaves per vertex

`research/sN/simplify/coverage.md`.  Let `D = (h, M)` be a description whose pairs form a
forest (`LeafProp`) with a child selector (`child m ∈ m`, injective on `M`), and let
`κ_o = h_o + #{(o, x) ∈ M}`.  An *out-leaf* is a vertex on exactly one pair with `κ = 1`.
If every vertex is adjacent to at most `s` out-leaves (`OutLeafBound D s`), then `D`
passes at most `(16(s+1)/3)^k k! (N-k)!` localities of order `k`
(`card_dpasses_le_of_outLeaf`).

For a passed locality with tie set `T`, put `H = {κ ≥ 1}` and
`Y` = untied vertices with an untied child.
* **(L1)** `T` is determined by `T ∩ H` (`tieSet_eq_of_inter_eq`): a vertex with `κ ≤ 0`
  is tied iff `κ ≠ 0` or it has a neighbour with `κ ≤ 0` or a tied neighbour.
* **(L2)** `|H \ T| ≤ (s+1)(|T| + |Y|)` (`card_high_untied_le`): an untied vertex of `H`
  is in `Y`, or has a tied child (injective), or is an out-leaf of a vertex of `T ∪ Y`.
* **(L3)** a matching outside `T` with `|Y| ≤ 2|P|` (`exists_matching_untiedParents`):
  the chosen child pairs have degree `≤ 2`, and a forest of maximum degree `Δ` has a
  matching `P` with `|E| ≤ Δ|P|` (`exists_matching_of_leaf`).
With `β = 1 - 1/(4(s+1))`: `2^{-|P|} ≤ β^{|H| - |T ∩ H|} β^{-(s+1)k}`, and
`Σ_{X ⊆ H, |X| ≤ k} β^{|H|-|X|} ≤ (1-β)^{-k}` (binomial theorem).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Simplify

open MaxNN CountLower CountExp Trees

variable {N : ℕ}

/-! ## The class -/

/-- `u` is an *out-leaf* of `D`: it lies on exactly one pair and `κ_u = 1`. -/
def IsOutLeaf (D : Descr N) (u : Fin N) : Prop :=
  (incid D.M u).card = 1 ∧ DKappa D u = 1

/-- Every vertex is adjacent to at most `s` out-leaves. -/
def OutLeafBound (D : Descr N) (s : ℕ) : Prop :=
  ∀ v (U : Finset (Fin N)), (∀ u ∈ U, DAdj D v u ∧ IsOutLeaf D u) → U.card ≤ s

/-- The vertices with `κ ≥ 1`. -/
noncomputable def highSet (D : Descr N) : Finset (Fin N) := by
  classical
  exact univ.filter fun v => 1 ≤ DKappa D v

theorem mem_highSet {D : Descr N} {v : Fin N} : v ∈ highSet D ↔ 1 ≤ DKappa D v := by
  classical
  unfold highSet
  simp

/-! ## Elementary facts -/

theorem dkappa_le_zero_of_lt_one (D : Descr N) {v : Fin N} (h : DKappa D v < 1) :
    DKappa D v ≤ 0 := by
  have e : DKappa D v = ((D.h v + ((D.M.filter fun m => m.1 = v).card : ℤ) : ℤ) : ℝ) := by
    unfold DKappa
    push_cast
    ring
  rw [e] at h ⊢
  have h' : D.h v + ((D.M.filter fun m => m.1 = v).card : ℤ) < 1 := by exact_mod_cast h
  have : D.h v + ((D.M.filter fun m => m.1 = v).card : ℤ) ≤ 0 := by omega
  exact_mod_cast this

theorem not_dadj_self {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) (v : Fin N) :
    ¬ DAdj D v v := by
  rintro (h | h) <;> exact lt_irrefl _ (hlt _ h)

theorem upCount_pos {D : Descr N} {π : Equiv.Perm (Fin N)} {v w : Fin N}
    (hadj : DAdj D v w) (hlt : π w < π v) : 0 < upCount (DAdj D) π v := by
  classical
  unfold upCount
  exact card_pos.mpr ⟨w, mem_filter.mpr ⟨mem_univ _, hadj, hlt⟩⟩

/-- An untied vertex has at most as many neighbours above as pairs. -/
theorem upCount_le_incid {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (π : Equiv.Perm (Fin N)) (u : Fin N) : upCount (DAdj D) π u ≤ (incid D.M u).card := by
  classical
  unfold upCount
  refine (card_le_of_subset ?_).trans
    (card_image_le (s := incid D.M u) (f := fun m => if m.1 = u then m.2 else m.1))
  intro x hx
  obtain ⟨-, hadj, -⟩ := mem_filter.mp hx
  rw [mem_image]
  rcases hadj with h | h
  · exact ⟨(u, x), mem_filter.mpr ⟨h, Or.inl rfl⟩, by simp⟩
  · refine ⟨(x, u), mem_filter.mpr ⟨h, Or.inr rfl⟩, ?_⟩
    have hxu : x ≠ u := ne_of_lt (hlt _ h)
    simp [hxu]

theorem upCount_eq_zero_of_nonpos {D : Descr N} {k : ℕ} {π : Equiv.Perm (Fin N)}
    (hb : Balanced (DAdj D) (DKappa D) k π) {v : Fin N} (hv : v ∉ tieSet k π)
    (hκ : DKappa D v ≤ 0) : upCount (DAdj D) π v = 0 ∧ DKappa D v = 0 := by
  have hvk : k ≤ ((π v : Fin N) : ℕ) := by
    by_contra h
    exact hv (mem_tieSet'.mpr (by omega))
  have h1 := hb v hvk
  have h0 : (0 : ℝ) ≤ upCount (DAdj D) π v := Nat.cast_nonneg _
  have hz : (upCount (DAdj D) π v : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast hz, by linarith⟩

/-! ## (L1) The tie set is determined by its vertices with `κ ≥ 1` -/

/-- A vertex with `κ ≤ 0` is tied iff `κ ≠ 0` or it has a neighbour with `κ ≤ 0` or a tied
neighbour. -/
theorem mem_tieSet_iff_of_nonpos {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) {k : ℕ}
    {π : Equiv.Perm (Fin N)} (hp : DPasses D k π) {v : Fin N} (hv : DKappa D v ≤ 0) :
    v ∈ tieSet k π ↔
      DKappa D v ≠ 0 ∨ ∃ w, DAdj D v w ∧ (DKappa D w ≤ 0 ∨ w ∈ tieSet k π) := by
  constructor
  · intro hvT
    by_contra hcon
    push_neg at hcon
    exact hp.2 v (mem_tieSet'.mp hvT)
      (fun x hx hadj => (hcon.2 x hadj).2 (mem_tieSet'.mpr hx)) hcon.1
  · intro hcase
    by_contra hvT
    obtain ⟨hup, hκ0⟩ := upCount_eq_zero_of_nonpos hp.1 hvT hv
    have hnot : ∀ w, DAdj D v w → ¬ π w < π v := fun w hw hwv => by
      have := upCount_pos hw hwv
      omega
    rcases hcase with h | ⟨w, hw, hw' | hwT⟩
    · exact h hκ0
    · by_cases hwT : w ∈ tieSet k π
      · exact hnot w hw (upCount_lt_of_mem hwT hvT)
      · obtain ⟨hupw, -⟩ := upCount_eq_zero_of_nonpos hp.1 hwT hw'
        have hvw : ¬ π v < π w := fun h => by
          have := upCount_pos (dadj_symm hw) h
          omega
        have hne : π v ≠ π w := fun h => by
          have e := π.injective h
          subst e
          exact not_dadj_self hlt v hw
        rcases lt_or_gt_of_ne hne with h | h
        · exact hvw h
        · exact hnot w hw h
    · exact hnot w hw (upCount_lt_of_mem hwT hvT)

/-- **(L1)** Two passed localities whose tie sets agree on `{κ ≥ 1}` have the same tie set. -/
theorem tieSet_eq_of_inter_eq {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) {k : ℕ}
    {π π' : Equiv.Perm (Fin N)} (hp : DPasses D k π) (hp' : DPasses D k π')
    (h : tieSet k π ∩ highSet D = tieSet k π' ∩ highSet D) : tieSet k π = tieSet k π' := by
  have hH : ∀ w, 1 ≤ DKappa D w → (w ∈ tieSet k π ↔ w ∈ tieSet k π') := by
    intro w hw
    have hwH : w ∈ highSet D := mem_highSet.mpr hw
    constructor <;> intro hx
    · have := mem_inter.mpr ⟨hx, hwH⟩
      rw [h] at this
      exact (mem_inter.mp this).1
    · have := mem_inter.mpr ⟨hx, hwH⟩
      rw [← h] at this
      exact (mem_inter.mp this).1
  ext v
  by_cases hv : 1 ≤ DKappa D v
  · exact hH v hv
  · have hv0 := dkappa_le_zero_of_lt_one D (not_le.mp hv)
    rw [mem_tieSet_iff_of_nonpos hlt hp hv0, mem_tieSet_iff_of_nonpos hlt hp' hv0]
    have key : ∀ w, (DKappa D w ≤ 0 ∨ w ∈ tieSet k π) ↔ (DKappa D w ≤ 0 ∨ w ∈ tieSet k π') := by
      intro w
      by_cases hw : 1 ≤ DKappa D w
      · rw [hH w hw]
      · have := dkappa_le_zero_of_lt_one D (not_le.mp hw)
        exact iff_of_true (Or.inl this) (Or.inl this)
    simp only [key]

/-! ## Child pairs -/

/-- `m` is a pair of `D` at `y` whose child endpoint is not `y`: it joins `y` to a child. -/
def ChildPair (D : Descr N) (child : Fin N × Fin N → Fin N) (y : Fin N)
    (m : Fin N × Fin N) : Prop :=
  m ∈ D.M ∧ (m.1 = y ∨ m.2 = y) ∧ child m ≠ y

theorem childPair_ends {D : Descr N} {child : Fin N × Fin N → Fin N}
    (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2) {y : Fin N} {m : Fin N × Fin N}
    (h : ChildPair D child y m) {z : Fin N} (hz : m.1 = z ∨ m.2 = z) :
    z = y ∨ z = child m := by
  obtain ⟨hm, hy, hc⟩ := h
  rcases hchild m hm with e | e <;> rcases hy with hy | hy
  · exact absurd (e.trans hy) hc
  · rcases hz with hz | hz
    · exact Or.inr (hz.symm.trans e.symm)
    · exact Or.inl (hz.symm.trans hy)
  · rcases hz with hz | hz
    · exact Or.inl (hz.symm.trans hy)
    · exact Or.inr (hz.symm.trans e.symm)
  · exact absurd (e.trans hy) hc

theorem childPair_unique {D : Descr N} {child : Fin N × Fin N → Fin N}
    (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2) {y y' : Fin N} {m : Fin N × Fin N}
    (h : ChildPair D child y m) (h' : ChildPair D child y' m) : y = y' := by
  rcases childPair_ends hchild h h'.2.1 with e | e
  · exact e.symm
  · exact absurd e.symm h'.2.2

/-- The untied vertices with an untied child. -/
noncomputable def untiedParents (D : Descr N) (child : Fin N × Fin N → Fin N)
    (T : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact univ.filter fun y => y ∉ T ∧ ∃ m, ChildPair D child y m ∧ child m ∉ T

theorem mem_untiedParents {D : Descr N} {child : Fin N × Fin N → Fin N} {T : Finset (Fin N)}
    {y : Fin N} :
    y ∈ untiedParents D child T ↔ y ∉ T ∧ ∃ m, ChildPair D child y m ∧ child m ∉ T := by
  classical
  unfold untiedParents
  simp

/-! ## (L2) Counting the untied vertices with `κ ≥ 1` -/

/-- **(L2)** `|H \ T| ≤ (s+1)(|T| + |Y|)`. -/
theorem card_high_untied_le (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (child : Fin N × Fin N → Fin N) (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2)
    (hcinj : Set.InjOn child D.M) {s : ℕ} (hs : OutLeafBound D s) {k : ℕ}
    {π : Equiv.Perm (Fin N)} (hb : Balanced (DAdj D) (DKappa D) k π) :
    (highSet D \ tieSet k π).card ≤
      (s + 1) * ((tieSet k π).card + (untiedParents D child (tieSet k π)).card) := by
  classical
  set T := tieSet k π
  set Y := untiedParents D child T
  set R := highSet D \ T
  set A := R.filter fun u => u ∈ Y
  set B := R.filter fun u => u ∉ Y ∧ ∃ m, ChildPair D child u m
  set C := R.filter fun u => u ∉ Y ∧ ¬ ∃ m, ChildPair D child u m
  have hR : R.card ≤ A.card + B.card + C.card := by
    have hsub : R ⊆ A ∪ B ∪ C := by
      intro u hu
      by_cases h1 : u ∈ Y
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hu, h1⟩))
      · by_cases h2 : ∃ m, ChildPair D child u m
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hu, h1, h2⟩))
        · exact mem_union_right _ (mem_filter.mpr ⟨hu, h1, h2⟩)
    exact (card_le_of_subset hsub).trans
      ((card_union_le _ _).trans (add_le_add_right (card_union_le _ _) _))
  have hA : A.card ≤ Y.card := card_le_of_subset fun u hu => (mem_filter.mp hu).2
  -- an untied vertex with a tied child: injective via the child
  have hB : B.card ≤ T.card := by
    apply card_le_card_of_forall_subsingleton
      (fun u t => ∃ m, ChildPair D child u m ∧ child m = t)
    · intro u hu
      obtain ⟨huR, huY, m, hm⟩ := mem_filter.mp hu
      have huT : u ∉ T := (mem_sdiff.mp huR).2
      refine ⟨child m, ?_, m, hm, rfl⟩
      by_contra hcT
      exact huY (mem_untiedParents.mpr ⟨huT, m, hm, hcT⟩)
    · intro t _ u hu u' hu'
      obtain ⟨m, hm, hmt⟩ := hu.2
      obtain ⟨m', hm', hmt'⟩ := hu'.2
      have hmm : m = m' := hcinj hm.1 hm'.1 (hmt.trans hmt'.symm)
      subst hmm
      exact childPair_unique hchild hm hm'
  -- the remaining vertices are out-leaves of a vertex of `T ∪ Y`
  have hCleaf : ∀ u ∈ C, IsOutLeaf D u := by
    intro u hu
    obtain ⟨huR, -, hnc⟩ := mem_filter.mp hu
    have hκ : 1 ≤ DKappa D u := mem_highSet.mp (mem_sdiff.mp huR).1
    have huT : u ∉ T := (mem_sdiff.mp huR).2
    have huk : k ≤ ((π u : Fin N) : ℕ) := by
      by_contra h
      exact huT (mem_tieSet'.mpr (by omega))
    have hup := hb u huk
    -- every pair at `u` has child `u`
    have hpairs : ∀ m ∈ incid D.M u, child m = u := by
      intro m hm
      obtain ⟨hmM, hmu⟩ := mem_filter.mp hm
      by_contra hc
      exact hnc ⟨m, hmM, hmu, hc⟩
    have hle1 : (incid D.M u).card ≤ 1 :=
      card_le_one.mpr fun m hm m' hm' =>
        hcinj (mem_filter.mp hm).1 (mem_filter.mp hm').1 ((hpairs m hm).trans (hpairs m' hm').symm)
    have hupc := upCount_le_incid hlt π u
    have hup1 : (upCount (DAdj D) π u : ℝ) ≤ 1 := by exact_mod_cast hupc.trans hle1
    have hpos : 1 ≤ upCount (DAdj D) π u := by
      have : (1 : ℝ) ≤ upCount (DAdj D) π u := by rw [hup]; exact hκ
      exact_mod_cast this
    refine ⟨le_antisymm hle1 (le_trans hpos (hupc)), ?_⟩
    linarith
  have hCpar : ∀ u ∈ C, ∃ p, p ∈ T ∪ Y ∧ DAdj D p u := by
    intro u hu
    obtain ⟨huR, -, hnc⟩ := mem_filter.mp hu
    have hκ : 1 ≤ DKappa D u := mem_highSet.mp (mem_sdiff.mp huR).1
    have huT : u ∉ T := (mem_sdiff.mp huR).2
    have huk : k ≤ ((π u : Fin N) : ℕ) := by
      by_contra h
      exact huT (mem_tieSet'.mpr (by omega))
    have hup := hb u huk
    have hpos : 0 < upCount (DAdj D) π u := by
      have : (0 : ℝ) < upCount (DAdj D) π u := by rw [hup]; linarith
      exact_mod_cast this
    obtain ⟨w, hw⟩ := card_pos.mp (by unfold upCount at hpos; exact hpos)
    have hwadj : DAdj D u w := (mem_filter.mp hw).2.1
    refine ⟨w, ?_, dadj_symm hwadj⟩
    by_cases hwT : w ∈ T
    · exact mem_union_left _ hwT
    · refine mem_union_right _ (mem_untiedParents.mpr ⟨hwT, ?_⟩)
      -- the pair `m` joining `u` and `w` has child `u`
      have hwu : w ≠ u := fun e => not_dadj_self hlt u (e ▸ hwadj)
      obtain ⟨m, hmM, hm1, hm2⟩ : ∃ m ∈ D.M, (m.1 = u ∨ m.2 = u) ∧ (m.1 = w ∨ m.2 = w) := by
        rcases hwadj with h | h
        · exact ⟨_, h, Or.inl rfl, Or.inr rfl⟩
        · exact ⟨_, h, Or.inr rfl, Or.inl rfl⟩
      have hcu : child m = u := by
        by_contra hc
        exact hnc ⟨m, hmM, hm1, hc⟩
      exact ⟨m, ⟨hmM, hm2, hcu ▸ hwu.symm⟩, hcu ▸ huT⟩
  have hC : C.card ≤ s * (T ∪ Y).card := by
    have := card_mul_le_card_mul (s := C) (t := T ∪ Y) (m := 1) (n := s)
      (fun u p => DAdj D p u)
      (fun u hu => by
        obtain ⟨p, hp, hadj⟩ := hCpar u hu
        exact card_pos.mpr ⟨p, by rw [bipartiteAbove, mem_filter]; exact ⟨hp, hadj⟩⟩)
      (fun p _ => hs p _ fun u hu => by
        rw [bipartiteBelow, mem_filter] at hu
        exact ⟨hu.2, hCleaf u hu.1⟩)
    rw [mul_one, mul_comm] at this
    exact this
  have hTY : (T ∪ Y).card ≤ T.card + Y.card := card_union_le _ _
  have hC' : C.card ≤ s * (T.card + Y.card) := hC.trans (Nat.mul_le_mul_left _ hTY)
  calc R.card ≤ A.card + B.card + C.card := hR
    _ ≤ Y.card + T.card + s * (T.card + Y.card) := add_le_add (add_le_add hA hB) hC'
    _ = (s + 1) * (T.card + Y.card) := by ring

/-! ## (L3) A matching on the child pairs -/

/-- A forest of maximum degree `Δ` has a matching `P` with `|E| ≤ Δ |P|`. -/
theorem exists_matching_of_leaf {N Δ : ℕ} :
    ∀ n (E : Finset (Fin N × Fin N)), E.card = n → LeafProp E → (∀ o, (incid E o).card ≤ Δ) →
      ∃ P ⊆ E, VDisj P ∧ E.card ≤ Δ * P.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hEn hleaf hdeg
    rcases E.eq_empty_or_nonempty with hE | hne
    · exact ⟨∅, empty_subset _, fun p hp => absurd hp (not_mem_empty p), by simp [hE]⟩
    obtain ⟨m, hm, u, hu, huniq⟩ := hleaf E (Subset.refl _) hne
    -- `w`: the endpoint of `m` other than the leaf `u`
    obtain ⟨w, hw⟩ : ∃ w, ∀ x ∈ E, (x.1 = m.1 ∨ x.2 = m.1 ∨ x.1 = m.2 ∨ x.2 = m.2) →
        x.1 = w ∨ x.2 = w := by
      rcases hu with rfl | rfl
      · refine ⟨m.2, fun x hx hxm => ?_⟩
        by_cases hxu : x.1 = m.1 ∨ x.2 = m.1
        · have e := huniq x hx hxu
          rw [e]
          exact Or.inr rfl
        · push_neg at hxu
          tauto
      · refine ⟨m.1, fun x hx hxm => ?_⟩
        by_cases hxu : x.1 = m.2 ∨ x.2 = m.2
        · have e := huniq x hx hxu
          rw [e]
          exact Or.inl rfl
        · push_neg at hxu
          tauto
    set E' := E.filter fun m' => ¬ (m'.1 = m.1 ∨ m'.2 = m.1 ∨ m'.1 = m.2 ∨ m'.2 = m.2) with hE'
    have hsub : E \ E' ⊆ incid E w := by
      intro x hx
      rw [mem_sdiff, hE', mem_filter] at hx
      have hxE := hx.1
      have hxm : x.1 = m.1 ∨ x.2 = m.1 ∨ x.1 = m.2 ∨ x.2 = m.2 := by
        by_contra hc
        exact hx.2 ⟨hxE, hc⟩
      exact mem_filter.mpr ⟨hxE, hw x hxE hxm⟩
    have hcard1 : (E \ E').card ≤ Δ := (card_le_of_subset hsub).trans (hdeg w)
    have hmE' : m ∉ E' := by
      rw [hE', mem_filter]
      push_neg
      intro _
      exact Or.inl rfl
    have hE'sub : E' ⊆ E := filter_subset _ _
    have hlt : E'.card < n := by
      rw [← hEn]
      exact card_lt_card ⟨hE'sub, fun h => hmE' (h hm)⟩
    have hdeg' : ∀ o, (incid E' o).card ≤ Δ := fun o =>
      (card_le_of_subset (filter_subset_filter _ hE'sub)).trans (hdeg o)
    have hleaf' : LeafProp E' := fun F hF hFne => hleaf F (hF.trans hE'sub) hFne
    obtain ⟨P', hP'sub, hP'disj, hP'card⟩ := ih _ hlt E' rfl hleaf' hdeg'
    have hmP' : m ∉ P' := fun h => hmE' (hP'sub h)
    refine ⟨insert m P', insert_subset_iff.mpr ⟨hm, hP'sub.trans hE'sub⟩, ?_, ?_⟩
    · intro p hp p' hp' hpp'
      have far : ∀ q ∈ P', q.1 ≠ m.1 ∧ q.2 ≠ m.1 ∧ q.1 ≠ m.2 ∧ q.2 ≠ m.2 := by
        intro q hq
        have := (mem_filter.mp (hP'sub hq)).2
        push_neg at this
        exact this
      rcases mem_insert.mp hp with h1 | h1 <;> rcases mem_insert.mp hp' with h2 | h2
      · exact absurd (h1.trans h2.symm) hpp'
      · rw [h1]
        have := far p' h2
        exact ⟨this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm⟩
      · rw [h2]
        have := far p h1
        exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2⟩
      · exact hP'disj p h1 p' h2 hpp'
    · rw [card_insert_of_not_mem hmP']
      have hsplit : E.card = E'.card + (E \ E').card := by
        rw [add_comm, card_sdiff_add_card_eq_card hE'sub]
      rw [hsplit, mul_add, mul_one]
      exact add_le_add hP'card hcard1

/-- **(L3)** A matching of pairs outside `T` with `|Y| ≤ 2 |P|`. -/
theorem exists_matching_untiedParents (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (hleaf : LeafProp D.M) (child : Fin N × Fin N → Fin N)
    (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2) (hcinj : Set.InjOn child D.M)
    (T : Finset (Fin N)) :
    ∃ P ⊆ D.M, VDisj P ∧ (∀ m ∈ P, m.1 ∉ T ∧ m.2 ∉ T) ∧
      (untiedParents D child T).card ≤ 2 * P.card := by
  classical
  set Y := untiedParents D child T
  have hex : ∀ y, ∃ m : Fin N × Fin N, y ∈ Y → ChildPair D child y m ∧ child m ∉ T := by
    intro y
    by_cases h : y ∈ Y
    · obtain ⟨-, m, hm, hc⟩ := mem_untiedParents.mp h
      exact ⟨m, fun _ => ⟨hm, hc⟩⟩
    · exact ⟨(y, y), fun h' => absurd h' h⟩
  choose g hg using hex
  have hinj : Set.InjOn g Y := by
    intro y hy y' hy' he
    have h1 := (hg y hy).1
    have h2 := (hg y' hy').1
    rw [← he] at h2
    exact childPair_unique hchild h1 h2
  set E := Y.image g
  have hEY : E.card = Y.card := card_image_of_injOn hinj
  have hEM : E ⊆ D.M := by
    intro m hm
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hm
    exact (hg y hy).1.1
  have hends : ∀ y ∈ Y, ∀ z, ((g y).1 = z ∨ (g y).2 = z) → z = y ∨ z = child (g y) :=
    fun y hy z hz => childPair_ends hchild (hg y hy).1 hz
  have hEout : ∀ m ∈ E, m.1 ∉ T ∧ m.2 ∉ T := by
    intro m hm
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hm
    have hyT : y ∉ T := (mem_untiedParents.mp hy).1
    have hcT := (hg y hy).2
    constructor
    · rcases hends y hy _ (Or.inl rfl) with e | e <;> rw [e] <;> assumption
    · rcases hends y hy _ (Or.inr rfl) with e | e <;> rw [e] <;> assumption
  have hdeg : ∀ o, (incid E o).card ≤ 2 := by
    intro o
    have hsub : incid E o ⊆ insert (g o) (D.M.filter fun m => child m = o) := by
      intro x hx
      obtain ⟨hxE, hxo⟩ := mem_filter.mp hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hxE
      rcases hends y hy o hxo with e | e
      · rw [e]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_filter.mpr ⟨(hg y hy).1.1, e.symm⟩)
    have hfil : (D.M.filter fun m => child m = o).card ≤ 1 :=
      card_le_one.mpr fun m hm m' hm' =>
        hcinj (mem_filter.mp hm).1 (mem_filter.mp hm').1
          ((mem_filter.mp hm).2.trans (mem_filter.mp hm').2.symm)
    calc (incid E o).card ≤ (insert (g o) (D.M.filter fun m => child m = o)).card :=
          card_le_of_subset hsub
      _ ≤ (D.M.filter fun m => child m = o).card + 1 := card_insert_le _ _
      _ ≤ 2 := by omega
  have hleafE : LeafProp E := fun F hF hFne => hleaf F (hF.trans hEM) hFne
  obtain ⟨P, hPE, hPd, hPc⟩ := exists_matching_of_leaf _ E rfl hleafE hdeg
  exact ⟨P, hPE.trans hEM, hPd, fun m hm => hEout m (hPE hm), by rw [← hEY]; exact hPc⟩

/-! ## The generating function -/

/-- `Σ_{X ∈ S} β^{|H| - |X|} ≤ (1-β)^{-k}` for subsets `X ⊆ H` of size `≤ k`. -/
theorem sum_pow_sub_card_le {α : Type*} (H : Finset α) (S : Finset (Finset α))
    (hS : S ⊆ H.powerset) {k : ℕ} (hk : ∀ X ∈ S, X.card ≤ k) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : ∑ X in S, β ^ (H.card - X.card) ≤ ((1 - β)⁻¹) ^ k := by
  have hγ0 : 0 < 1 - β := by linarith
  have h3 : (1 - β) ^ k * ((1 - β)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel hγ0.ne', one_pow]
  have hterm : ∀ X ∈ S, β ^ (H.card - X.card) ≤
      (1 - β) ^ X.card * β ^ (H.card - X.card) * ((1 - β)⁻¹) ^ k := by
    intro X hX
    have h1 : (1 - β) ^ k ≤ (1 - β) ^ X.card :=
      pow_le_pow_of_le_one hγ0.le (by linarith) (hk X hX)
    have h2 : 1 ≤ (1 - β) ^ X.card * ((1 - β)⁻¹) ^ k :=
      calc (1 : ℝ) = (1 - β) ^ k * ((1 - β)⁻¹) ^ k := h3.symm
        _ ≤ (1 - β) ^ X.card * ((1 - β)⁻¹) ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
    have hb : 0 ≤ β ^ (H.card - X.card) := pow_nonneg hβ0 _
    calc β ^ (H.card - X.card) = β ^ (H.card - X.card) * 1 := by ring
      _ ≤ β ^ (H.card - X.card) * ((1 - β) ^ X.card * ((1 - β)⁻¹) ^ k) :=
          mul_le_mul_of_nonneg_left h2 hb
      _ = _ := by ring
  calc ∑ X in S, β ^ (H.card - X.card)
      ≤ ∑ X in S, (1 - β) ^ X.card * β ^ (H.card - X.card) * ((1 - β)⁻¹) ^ k :=
        sum_le_sum hterm
    _ ≤ ∑ X in H.powerset, (1 - β) ^ X.card * β ^ (H.card - X.card) * ((1 - β)⁻¹) ^ k :=
        sum_le_sum_of_subset_of_nonneg hS fun X _ _ => by positivity
    _ = ((1 - β)⁻¹) ^ k := by
        rw [← sum_mul, sum_pow_mul_eq_add_pow, sub_add_cancel, one_pow, one_mul]

/-- The weight `β = 1 - 1/(4(s+1))`: `β^(2(s+1)) ≥ 1/2` and `β^(s+1) ≥ 3/4`. -/
theorem beta_pow_ge (s n : ℕ) (hn : n ≤ 2 * (s + 1)) :
    1 - (n : ℝ) / (4 * ((s : ℝ) + 1)) ≤ (1 - 1 / (4 * ((s : ℝ) + 1))) ^ n := by
  have hs : (0 : ℝ) < 4 * ((s : ℝ) + 1) := by positivity
  have ha : (-2 : ℝ) ≤ -(1 / (4 * ((s : ℝ) + 1))) := by
    have : 1 / (4 * ((s : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one hs]
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      linarith
    linarith
  have := one_add_mul_le_pow ha n
  have e : 1 + (n : ℝ) * -(1 / (4 * ((s : ℝ) + 1))) = 1 - (n : ℝ) / (4 * ((s : ℝ) + 1)) := by
    ring
  rw [e, ← sub_eq_add_neg] at this
  exact this

/-! ## The per-unit count -/

open Classical in
/-- **Per-unit count.** A unit whose pairs form a forest with at most `s` out-leaves at
every vertex passes at most `(16(s+1)/3)^k k! (N-k)!` localities of order `k`. -/
theorem card_dpasses_le_of_outLeaf (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (hleaf : LeafProp D.M) (child : Fin N × Fin N → Fin N)
    (hchild : ∀ m ∈ D.M, child m = m.1 ∨ child m = m.2) (hcinj : Set.InjOn child D.M)
    {s : ℕ} (hs : OutLeafBound D s) {k : ℕ} (hk : k ≤ N) :
    (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ) ≤
      (16 * ((s : ℝ) + 1) / 3) ^ k * (k ! * (N - k)! : ℕ) := by
  classical
  set F := k ! * (N - k)!
  set H := highSet D
  set β : ℝ := 1 - 1 / (4 * ((s : ℝ) + 1)) with hβ
  have hs4 : (0 : ℝ) < 4 * ((s : ℝ) + 1) := by positivity
  have hq : 0 < 1 / (4 * ((s : ℝ) + 1)) := by positivity
  have hq4 : 1 / (4 * ((s : ℝ) + 1)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    linarith
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hβpos : 0 < β := by rw [hβ]; linarith
  have hhalf : (1 / 2 : ℝ) ≤ β ^ (2 * (s + 1)) := by
    have h := beta_pow_ge s (2 * (s + 1)) le_rfl
    have e : 1 - ((2 * (s + 1) : ℕ) : ℝ) / (4 * ((s : ℝ) + 1)) = 1 / 2 := by
      push_cast
      field_simp
      ring
    rw [e] at h
    exact h
  have h34 : (3 / 4 : ℝ) ≤ β ^ (s + 1) := by
    have h := beta_pow_ge s (s + 1) (by omega)
    have e : 1 - ((s + 1 : ℕ) : ℝ) / (4 * ((s : ℝ) + 1)) = 3 / 4 := by
      push_cast
      field_simp
      ring
    rw [e] at h
    exact h
  have hγ : (1 - β)⁻¹ = 4 * ((s : ℝ) + 1) := by
    rw [hβ, sub_sub_cancel, one_div, inv_inv]
  have hinvβ : (β ^ (s + 1))⁻¹ ≤ 4 / 3 := by
    rw [inv_le (by positivity) (by norm_num)]
    calc ((4 : ℝ) / 3)⁻¹ = 3 / 4 := by norm_num
      _ ≤ β ^ (s + 1) := h34
  -- the admissible tie sets
  set 𝒯 := ((univ : Finset (Fin N)).powersetCard k).filter fun T =>
    ∃ π, DPasses D k π ∧ tieSet k π = T
  have hcover : (univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k) ⊆
      𝒯.biUnion fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k) := by
    intro π hπ
    have hp := (mem_filter.mp hπ).2
    refine mem_biUnion.mpr ⟨tieSet k π, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, card_tieSet hk π⟩, π, hp, rfl⟩
    · simp only [fiber, mem_filter, mem_univ, true_and]
      exact hp.1
  -- each tie set
  have hper : ∀ T ∈ 𝒯, (((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card : ℝ) ≤
      F * (β ^ (H.card - (T ∩ H).card) * ((β ^ (s + 1))⁻¹) ^ k) := by
    intro T hT
    obtain ⟨hT1, π, hp, hπT⟩ := mem_filter.mp hT
    have hTk : T.card = k := (mem_powersetCard.mp hT1).2
    obtain ⟨P, hPM, hPd, hPout, hYP⟩ :=
      exists_matching_untiedParents D hlt hleaf child hchild hcinj T
    have hfib := card_balanced_fiber_of_matching D hlt hleaf hTk P hPM hPd hPout
    have hL2 := card_high_untied_le D hlt child hchild hcinj hs hp.1
    rw [hπT, hTk] at hL2
    have hsplit := card_sdiff_add_card_inter H T
    have hexp : H.card - (T ∩ H).card ≤ 2 * (s + 1) * P.card + (s + 1) * k := by
      rw [inter_comm]
      have h1 : (s + 1) * (k + (untiedParents D child T).card) ≤ (s + 1) * (k + 2 * P.card) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left hYP k)
      have h2 : (s + 1) * (k + 2 * P.card) = 2 * (s + 1) * P.card + (s + 1) * k := by ring
      have h3 : (H \ T).card ≤ 2 * (s + 1) * P.card + (s + 1) * k := hL2.trans (h1.trans h2.le)
      rw [← hsplit, Nat.add_sub_cancel]
      exact h3
    have h2p : (((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card : ℝ) *
        2 ^ P.card ≤ F := by exact_mod_cast hfib
    have hpos2 : (0 : ℝ) < 2 ^ P.card := by positivity
    have hβk : (0 : ℝ) < (β ^ (s + 1)) ^ k := by positivity
    have e1 : (1 / 2 : ℝ) ^ P.card ≤ β ^ (2 * (s + 1) * P.card) := by
      rw [pow_mul]
      exact pow_le_pow_left (by norm_num) hhalf _
    have e2 : β ^ (2 * (s + 1) * P.card) * (β ^ (s + 1)) ^ k ≤ β ^ (H.card - (T ∩ H).card) := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_of_le_one hβpos.le hβ1.le hexp
    have hpow : (1 / 2 : ℝ) ^ P.card ≤
        β ^ (H.card - (T ∩ H).card) * ((β ^ (s + 1))⁻¹) ^ k := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff hβk]
      exact (mul_le_mul_of_nonneg_right e1 hβk.le).trans e2
    have hfib' : (((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card : ℝ) ≤
        F * (1 / 2 : ℝ) ^ P.card := by
      rw [div_pow, one_pow, mul_one_div, le_div_iff hpos2]
      exact h2p
    exact hfib'.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
  -- the tie sets are determined by their `κ ≥ 1` part
  have hinj : Set.InjOn (fun T => T ∩ H) 𝒯 := by
    intro T hT T' hT' he
    obtain ⟨π, hp, rfl⟩ := (mem_filter.mp hT).2
    obtain ⟨π', hp', rfl⟩ := (mem_filter.mp hT').2
    exact tieSet_eq_of_inter_eq hlt hp hp' he
  have hsum : ∑ T in 𝒯, β ^ (H.card - (T ∩ H).card) ≤ ((1 - β)⁻¹) ^ k := by
    have himg : ∑ T in 𝒯, β ^ (H.card - (T ∩ H).card) =
        ∑ X in 𝒯.image (fun T => T ∩ H), β ^ (H.card - X.card) :=
      (sum_image (f := fun X => β ^ (H.card - X.card)) hinj).symm
    rw [himg]
    apply sum_pow_sub_card_le H _ _ _ hβpos.le hβ1
    · intro X hX
      obtain ⟨T, -, rfl⟩ := mem_image.mp hX
      exact mem_powerset.mpr (inter_subset_right _ _)
    · intro X hX
      obtain ⟨T, hT, rfl⟩ := mem_image.mp hX
      have hTk : T.card = k := (mem_powersetCard.mp (mem_filter.mp hT).1).2
      rw [← hTk]
      exact card_le_of_subset (inter_subset_left _ _)
  -- assemble
  have h1 := card_le_of_subset hcover
  have h2 := (card_biUnion_le (s := 𝒯)
    (t := fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k)))
  have h12 : (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ) ≤
      ∑ T in 𝒯, (((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card : ℝ) := by
    exact_mod_cast h1.trans h2
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ ((β ^ (s + 1))⁻¹) ^ k := by positivity
  calc (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ)
      ≤ ∑ T in 𝒯, F * (β ^ (H.card - (T ∩ H).card) * ((β ^ (s + 1))⁻¹) ^ k) :=
        h12.trans (sum_le_sum hper)
    _ = F * ((β ^ (s + 1))⁻¹) ^ k * ∑ T in 𝒯, β ^ (H.card - (T ∩ H).card) := by
        rw [mul_sum]
        refine sum_congr rfl fun T _ => ?_
        ring
    _ ≤ F * ((β ^ (s + 1))⁻¹) ^ k * ((1 - β)⁻¹) ^ k :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hF0 hc0)
    _ ≤ F * (4 / 3) ^ k * (4 * ((s : ℝ) + 1)) ^ k := by
        rw [hγ]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left (by positivity) hinvβ _) hF0
    _ = (16 * ((s : ℝ) + 1) / 3) ^ k * (F : ℕ) := by
        have e : (16 * ((s : ℝ) + 1) / 3) ^ k = (4 / 3) ^ k * (4 * ((s : ℝ) + 1)) ^ k := by
          rw [← mul_pow]
          ring_nf
        rw [e]
        ring

end MaxCaterpillar.Simplify
