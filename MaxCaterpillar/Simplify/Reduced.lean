import MaxCaterpillar.Trees.Hubs
import MaxCaterpillar.Simplify.StarCover
import MaxCaterpillar.Simplify.BlockSum

/-!
# Per-unit count for units with a reduced forest of bounded degree

`research/sN/simplify/exponential.md`, steps S4–S6.  For a description `D = (h, M)`
(integer head, pairs `i < j`, hinge graph a forest) a *pendant* is a vertex with exactly one
hinge neighbour and `κ = 0`; the *reduced forest* is the hinge graph without its pendants.
If the reduced forest has maximum degree `≤ Δ` (`RedDeg D Δ`, `Δ ≥ 2`), the unit passes at
most `k! (N-k)! (2Δ+2)^k` permutations (`card_passes_le_red`).

Proof: a passed tie set is determined by its trace on `Φ` (non-pendant, non-isolated
vertices); `Φ` is cut into blocks (stars of a star cover of the reduced forest, and lone
vertices with a pendant edge); each block contributes one edge outside the tie set to a
matching, which halves the balanced orders; the resulting weight factorises over the blocks
and every block weight is at most `1`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Simplify

open MaxNN CountLower CountExp Trees

section Reduced

open Classical

variable {N : ℕ}

/-- The hinge neighbours of `v`. -/
noncomputable def nbrs (D : Descr N) (v : Fin N) : Finset (Fin N) := univ.filter (DAdj D v)

/-- A pendant: exactly one hinge neighbour and `κ = 0`. -/
def IsPend (D : Descr N) (p : Fin N) : Prop := (nbrs D p).card = 1 ∧ DKappa D p = 0

/-- Adjacency of the reduced forest (hinge graph without pendants). -/
def RAdj (D : Descr N) (u v : Fin N) : Prop := DAdj D u v ∧ ¬ IsPend D u ∧ ¬ IsPend D v

/-- The reduced forest has maximum degree `≤ Δ`. -/
def RedDeg (D : Descr N) (Δ : ℕ) : Prop := ∀ v, (univ.filter (RAdj D v)).card ≤ Δ

/-- The free vertices: neither pendant nor isolated. -/
noncomputable def freeSet (D : Descr N) : Finset (Fin N) :=
  univ.filter fun v => ¬ IsPend D v ∧ (nbrs D v).Nonempty

theorem mem_nbrs {D : Descr N} {v x : Fin N} : x ∈ nbrs D v ↔ DAdj D v x := by
  unfold nbrs; simp

theorem dadj_irrefl {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) (v : Fin N) : ¬ DAdj D v v := by
  rintro (h | h) <;> exact lt_irrefl _ (hlt _ h)

theorem eq_of_pend {D : Descr N} {p v x : Fin N} (hp : IsPend D p) (hpv : DAdj D p v)
    (hpx : DAdj D p x) : x = v := by
  obtain ⟨a, ha⟩ := card_eq_one.mp hp.1
  have hv : v ∈ nbrs D p := mem_nbrs.mpr hpv
  have hx : x ∈ nbrs D p := mem_nbrs.mpr hpx
  rw [ha, mem_singleton] at hv hx
  rw [hv, hx]

/-! ## Forced vertices (step S4) -/

section Forced

variable {D : Descr N} {k : ℕ} {π : Equiv.Perm (Fin N)}

theorem upCount_pos' {o v : Fin N} (hadj : DAdj D o v) (hlt : π v < π o) :
    0 < upCount (DAdj D) π o := by
  unfold upCount
  exact card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hadj, hlt⟩⟩

theorem upCount_zero' {o : Fin N} (h : ∀ x, ¬ DAdj D o x) : upCount (DAdj D) π o = 0 := by
  unfold upCount
  rw [card_eq_zero, filter_eq_empty_iff]
  exact fun x _ hx => h x hx.1

theorem not_mem_tie {o : Fin N} (h : o ∉ tieSet k π) : k ≤ ((π o : Fin N) : ℕ) := by
  rw [mem_tieSet'] at h; omega

theorem mem_tie_of_iso (hπ : DPasses D k π) {o : Fin N} (ho : ∀ x, ¬ DAdj D o x) :
    o ∈ tieSet k π ↔ DKappa D o ≠ 0 := by
  constructor
  · intro hoT
    exact hπ.2 o (mem_tieSet'.mp hoT) fun x _ => ho x
  · intro hκ
    by_contra hoT
    have hb := hπ.1 o (not_mem_tie hoT)
    rw [upCount_zero' ho] at hb
    exact hκ (by rw [← hb]; norm_num)

theorem pend_mem_iff (hπ : DPasses D k π) {p v : Fin N} (hp : IsPend D p) (hpv : DAdj D p v) :
    p ∈ tieSet k π ↔ v ∈ tieSet k π := by
  constructor
  · intro hpT
    by_contra hvT
    refine hπ.2 p (mem_tieSet'.mp hpT) (fun x hx hadj => hvT ?_) hp.2
    rw [← eq_of_pend hp hpv hadj]
    exact mem_tieSet'.mpr hx
  · intro hvT
    by_contra hpT
    have hb := hπ.1 p (not_mem_tie hpT)
    have hpos := upCount_pos' (π := π) hpv (upCount_lt_of_mem hvT hpT)
    rw [hp.2] at hb
    have : (0 : ℝ) < upCount (DAdj D) π p := by exact_mod_cast hpos
    linarith

theorem pend_pend_mem (hlt : ∀ m ∈ D.M, m.1 < m.2) (hπ : DPasses D k π) {p v : Fin N}
    (hp : IsPend D p) (hv : IsPend D v) (hpv : DAdj D p v) : p ∈ tieSet k π := by
  by_contra hpT
  have hvT : v ∉ tieSet k π := fun h => hpT ((pend_mem_iff hπ hp hpv).mpr h)
  have hne : p ≠ v := fun h => dadj_irrefl hlt p (h ▸ hpv)
  rcases lt_or_gt_of_ne (fun h => hne (π.injective h)) with h | h
  · have hb := hπ.1 v (not_mem_tie hvT)
    have hpos := upCount_pos' (π := π) (dadj_symm hpv) h
    rw [hv.2] at hb
    have : (0 : ℝ) < upCount (DAdj D) π v := by exact_mod_cast hpos
    linarith
  · have hb := hπ.1 p (not_mem_tie hpT)
    have hpos := upCount_pos' (π := π) hpv h
    rw [hp.2] at hb
    have : (0 : ℝ) < upCount (DAdj D) π p := by exact_mod_cast hpos
    linarith

/-- A passed tie set is determined by its free vertices. -/
theorem tie_eq_of_inter (hlt : ∀ m ∈ D.M, m.1 < m.2) {π' : Equiv.Perm (Fin N)}
    (hπ : DPasses D k π) (hπ' : DPasses D k π')
    (he : tieSet k π ∩ freeSet D = tieSet k π' ∩ freeSet D) : tieSet k π = tieSet k π' := by
  have hΦ : ∀ v ∈ freeSet D, (v ∈ tieSet k π ↔ v ∈ tieSet k π') := by
    intro v hv
    constructor
    · intro h
      have : v ∈ tieSet k π ∩ freeSet D := mem_inter.mpr ⟨h, hv⟩
      rw [he] at this; exact (mem_inter.mp this).1
    · intro h
      have : v ∈ tieSet k π' ∩ freeSet D := mem_inter.mpr ⟨h, hv⟩
      rw [← he] at this; exact (mem_inter.mp this).1
  ext o
  by_cases hiso : ∀ x, ¬ DAdj D o x
  · rw [mem_tie_of_iso hπ hiso, mem_tie_of_iso hπ' hiso]
  push_neg at hiso
  obtain ⟨v, hov⟩ := hiso
  by_cases hpo : IsPend D o
  · by_cases hpv : IsPend D v
    · exact iff_of_true (pend_pend_mem hlt hπ hpo hpv hov) (pend_pend_mem hlt hπ' hpo hpv hov)
    · have hvΦ : v ∈ freeSet D :=
        mem_filter.mpr ⟨mem_univ _, hpv, ⟨o, mem_nbrs.mpr (dadj_symm hov)⟩⟩
      rw [pend_mem_iff hπ hpo hov, pend_mem_iff hπ' hpo hov]
      exact hΦ v hvΦ
  · exact hΦ o (mem_filter.mpr ⟨mem_univ _, hpo, ⟨v, mem_nbrs.mpr hov⟩⟩)

end Forced

/-! ## The per-unit count (steps S5, S6) -/

/-- The ordered pair `(min, max)`. -/
def ord2 (u v : Fin N) : Fin N × Fin N := if u < v then (u, v) else (v, u)

theorem ord2_mem {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) {u v : Fin N} (h : DAdj D u v) :
    ord2 u v ∈ D.M := by
  unfold ord2
  rcases h with h | h
  · rw [if_pos (hlt _ h)]; exact h
  · rw [if_neg (not_lt.mpr (hlt _ h).le)]; exact h

theorem ord2_cases (u v : Fin N) :
    ((ord2 u v).1 = u ∨ (ord2 u v).1 = v) ∧ ((ord2 u v).2 = u ∨ (ord2 u v).2 = v) := by
  unfold ord2; split_ifs <;> simp

/-- **Per-unit count.** A unit whose hinge graph is a forest with a reduced forest of maximum
degree `≤ Δ` (`Δ ≥ 2`) passes at most `k! (N-k)! (2Δ+2)^k` permutations. -/
theorem card_passes_le_red (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2) (hleaf : LeafProp D.M)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hred : RedDeg D Δ) {k : ℕ} (hk : k ≤ N) :
    ((univ.filter (DPasses D k)).card : ℝ) ≤ (k ! * (N - k)! : ℕ) * (2 * Δ + 2 : ℝ) ^ k := by
  -- the star cover of the reduced forest
  have hRsymm : ∀ u v, RAdj D u v → RAdj D v u := fun u v h => ⟨dadj_symm h.1, h.2.2, h.2.1⟩
  have hRirr : ∀ v, ¬ RAdj D v v := fun v h => dadj_irrefl hlt v h.1
  obtain ⟨ctr, hctr⟩ := exists_starCover (RAdj D) hRsymm hRirr
  set Φ := freeSet D with hΦdef
  set V0 : Finset (Fin N) := univ.filter fun v => ∃ w, RAdj D v w with hV0
  have mem_V0 : ∀ {v}, v ∈ V0 ↔ ∃ w, RAdj D v w := fun {v} => by simp [hV0]
  have hV0Φ : ∀ v ∈ V0, v ∈ Φ := by
    intro v hv
    obtain ⟨w, hw⟩ := mem_V0.mp hv
    exact mem_filter.mpr ⟨mem_univ _, hw.2.1, ⟨w, mem_nbrs.mpr hw.1⟩⟩
  set I := Φ.filter fun v => v ∉ V0 ∨ ctr v = v with hI
  set blk : Fin N → Finset (Fin N) := fun i => if i ∈ V0 then V0.filter fun v => ctr v = i else {i}
  have hIΦ : ∀ i ∈ I, i ∈ Φ := fun i hi => (mem_filter.mp hi).1
  have hblkΦ : ∀ i ∈ I, blk i ⊆ Φ := by
    intro i hi v hv
    by_cases hiV : i ∈ V0
    · change v ∈ (if i ∈ V0 then V0.filter (fun v => ctr v = i) else {i}) at hv
      rw [if_pos hiV, mem_filter] at hv
      exact hV0Φ v hv.1
    · simp only [blk, hiV, if_false, mem_singleton] at hv
      rw [hv]; exact hIΦ i hi
  have hself : ∀ i ∈ I, i ∈ blk i := by
    intro i hi
    by_cases hiV : i ∈ V0
    · have hc : ctr i = i := ((mem_filter.mp hi).2.resolve_left (not_not.mpr hiV))
      simp only [blk, hiV, if_true]
      exact mem_filter.mpr ⟨hiV, hc⟩
    · simp only [blk, hiV, if_false, mem_singleton]
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (blk i) (blk j) := by
    intro i hi j hj hij
    rw [disjoint_left]
    intro v hvi hvj
    change v ∈ (if i ∈ V0 then V0.filter (fun v => ctr v = i) else {i}) at hvi
    change v ∈ (if j ∈ V0 then V0.filter (fun v => ctr v = j) else {j}) at hvj
    by_cases hiV : i ∈ V0 <;> by_cases hjV : j ∈ V0
    · rw [if_pos hiV, mem_filter] at hvi
      rw [if_pos hjV, mem_filter] at hvj
      exact hij (hvi.2.symm.trans hvj.2)
    · rw [if_pos hiV, mem_filter] at hvi
      rw [if_neg hjV, mem_singleton] at hvj
      exact hjV (hvj ▸ hvi.1)
    · rw [if_neg hiV, mem_singleton] at hvi
      rw [if_pos hjV, mem_filter] at hvj
      exact hiV (hvi ▸ hvj.1)
    · rw [if_neg hiV, mem_singleton] at hvi
      rw [if_neg hjV, mem_singleton] at hvj
      exact hij (hvi.symm.trans hvj)
  have hunion : I.biUnion blk = Φ := by
    apply Subset.antisymm
    · intro v hv
      obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
      exact hblkΦ i hi hvi
    · intro v hv
      by_cases hvV : v ∈ V0
      · obtain ⟨hc1, hc2, -, -⟩ := hctr v (mem_V0.mp hvV)
        have hcV : ctr v ∈ V0 := mem_V0.mpr hc1
        refine mem_biUnion.mpr ⟨ctr v, mem_filter.mpr ⟨hV0Φ _ hcV, Or.inr hc2⟩, ?_⟩
        simp only [blk, if_pos hcV]
        exact mem_filter.mpr ⟨hvV, rfl⟩
      · refine mem_biUnion.mpr ⟨v, mem_filter.mpr ⟨hv, Or.inl hvV⟩, ?_⟩
        simp only [blk, if_neg hvV, mem_singleton]
  -- leaves of a star
  have hleaves : ∀ i ∈ I, i ∈ V0 → ∀ v ∈ (blk i).erase i, RAdj D i v := by
    intro i hi hiV v hv
    obtain ⟨hvi, hvb⟩ := mem_erase.mp hv
    change v ∈ (if i ∈ V0 then V0.filter (fun v => ctr v = i) else {i}) at hvb
    rw [if_pos hiV, mem_filter] at hvb
    obtain ⟨-, -, h3, -⟩ := hctr v (mem_V0.mp hvb.1)
    have := h3 (by rw [hvb.2]; exact hvi.symm)
    rwa [hvb.2] at this
  have hstar_card : ∀ i ∈ I, i ∈ V0 → 1 ≤ ((blk i).erase i).card ∧ ((blk i).erase i).card ≤ Δ := by
    intro i hi hiV
    have hc : ctr i = i := ((mem_filter.mp hi).2.resolve_left (not_not.mpr hiV))
    constructor
    · obtain ⟨-, -, -, h4⟩ := hctr i (mem_V0.mp hiV)
      obtain ⟨w, hwi, hw, hcw⟩ := h4 hc
      refine card_pos.mpr ⟨w, mem_erase.mpr ⟨hwi, ?_⟩⟩
      simp only [blk, hiV, if_true]
      exact mem_filter.mpr ⟨mem_V0.mpr hw, hcw⟩
    · refine le_trans (card_le_of_subset fun v hv => ?_) (hred i)
      exact mem_filter.mpr ⟨mem_univ _, hleaves i hi hiV v hv⟩
  -- lone vertices: every hinge neighbour is a pendant
  have hlone : ∀ i ∈ I, i ∉ V0 → ∀ x, DAdj D i x → IsPend D x := by
    intro i hi hiV x hx
    by_contra hpx
    have hpi : ¬ IsPend D i := (mem_filter.mp (hIΦ i hi)).2.1
    exact hiV (mem_V0.mpr ⟨x, hx, hpi, hpx⟩)
  have hlone_ne : ∀ i ∈ I, (nbrs D i).Nonempty := fun i hi => (mem_filter.mp (hIΦ i hi)).2.2
  set pd : Fin N → Fin N := fun i => if h : (nbrs D i).Nonempty then (nbrs D i).min' h else i
  have hpd : ∀ i ∈ I, DAdj D i (pd i) := by
    intro i hi
    simp only [pd, dif_pos (hlone_ne i hi)]
    exact mem_nbrs.mp (min'_mem _ _)
  -- the block weights
  set y : ℝ := 1 / (2 * Δ + 2) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one (by positivity)]
    have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    linarith
  set chosen : Fin N → Finset (Fin N) → Prop :=
    fun i S => i ∉ S ∧ (i ∉ V0 ∨ ∃ l ∈ (blk i).erase i, l ∉ S) with hchosen
  set g : Fin N → Finset (Fin N) → ℝ :=
    fun i S => y ^ S.card * (if chosen i S then (1 / 2 : ℝ) else 1) with hg
  have hblock : ∀ i ∈ I, ∑ S in (blk i).powerset, g i S ≤ 1 := by
    intro i hi
    by_cases hiV : i ∈ V0
    · set L := (blk i).erase i
      have hiL : i ∉ L := not_mem_erase i _
      have hbL : blk i = insert i L := (insert_erase (hself i hi)).symm
      have hcongr : ∀ S ∈ (blk i).powerset, g i S =
          y ^ S.card * (if i ∉ S ∧ ∃ l ∈ L, l ∉ S then (1 / 2 : ℝ) else 1) := by
        intro S _
        simp only [hg, hchosen, hiV, not_true, false_or]
      rw [sum_congr rfl hcongr, hbL, star_sum i L hiL y]
      obtain ⟨h1, h2⟩ := hstar_card i hi hiV
      exact star_weight_le_one hΔ h1 h2
    · have hb : blk i = {i} := by simp only [blk, hiV, if_false]
      have hcongr : ∀ S ∈ (blk i).powerset, g i S =
          y ^ S.card * (if i ∉ S then (1 / 2 : ℝ) else 1) := by
        intro S _
        simp only [hg, hchosen, hiV, not_false_eq_true, true_or, and_true]
      rw [sum_congr rfl hcongr, hb, single_sum i y]
      have : y ≤ 1 / 6 := by
        rw [hy]; apply div_le_div_of_le_left (by norm_num) (by norm_num)
        have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
        linarith
      linarith
  -- the number of chosen blocks of a trace `A`
  set μ : Finset (Fin N) → ℕ := fun A => (I.filter fun i => chosen i (A ∩ blk i)).card with hμ
  -- the weight of a trace factorises
  have hfact : ∀ A ⊆ Φ, ∏ i in I, g i (A ∩ blk i) = y ^ A.card * (1 / 2 : ℝ) ^ μ A := by
    intro A hA
    have hcardA : ∑ i in I, (A ∩ blk i).card = A.card := by
      rw [← card_biUnion]
      · congr 1
        rw [← inter_biUnion, hunion, inter_eq_left.mpr hA]
      · intro i hi j hj hij
        exact disjoint_of_subset_left (inter_subset_right _ _)
          (disjoint_of_subset_right (inter_subset_right _ _) (hdisj i hi j hj hij))
    simp only [hg]
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, hcardA, prod_ite, prod_const, prod_const_one,
      mul_one]
  -- per tie set: a matching outside `T` with `μ` edges
  set Pass := univ.filter (DPasses D k)
  set 𝒯 := Pass.image (tieSet k)
  set F := k ! * (N - k)!
  have hper : ∀ T ∈ 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card *
      2 ^ μ (T ∩ Φ) ≤ F := by
    intro T hT
    obtain ⟨π, hπP, rfl⟩ := mem_image.mp hT
    have hπ : DPasses D k π := (mem_filter.mp hπP).2
    set T := tieSet k π
    have hTk : T.card = k := card_tieSet hk π
    have hcT : ∀ i ∈ I, (chosen i (T ∩ Φ ∩ blk i) ↔
        i ∉ T ∧ (i ∉ V0 ∨ ∃ l ∈ (blk i).erase i, l ∉ T)) := by
      intro i hi
      have hsub := hblkΦ i hi
      have e : T ∩ Φ ∩ blk i = T ∩ blk i := by
        rw [inter_assoc, inter_eq_right.mpr hsub]
      simp only [hchosen, e, mem_inter, not_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun h => h1 h (hself i hi), ?_⟩
        rcases h2 with h2 | ⟨l, hl, hl'⟩
        · exact Or.inl h2
        · exact Or.inr ⟨l, hl, fun h => hl' h (mem_of_mem_erase hl)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun h _ => h1 h, ?_⟩
        rcases h2 with h2 | ⟨l, hl, hl'⟩
        · exact Or.inl h2
        · exact Or.inr ⟨l, hl, fun h _ => hl' h⟩
    set C := I.filter fun i => chosen i (T ∩ Φ ∩ blk i)
    -- the partner of a chosen block
    set part : Fin N → Fin N := fun i =>
      if i ∈ V0 then
        (if h : (((blk i).erase i).filter fun l => l ∉ T).Nonempty then
          (((blk i).erase i).filter fun l => l ∉ T).min' h else i)
      else pd i
    have hpart : ∀ i ∈ C, DAdj D i (part i) ∧ i ∉ T ∧ part i ∉ T ∧
        (i ∈ V0 → part i ∈ blk i) ∧ (i ∉ V0 → part i = pd i) := by
      intro i hiC
      obtain ⟨hi, hch⟩ := mem_filter.mp hiC
      obtain ⟨hiT, hrest⟩ := (hcT i hi).mp hch
      by_cases hiV : i ∈ V0
      · obtain ⟨l, hl, hlT⟩ := hrest.resolve_left (not_not.mpr hiV)
        have hne : (((blk i).erase i).filter fun l => l ∉ T).Nonempty :=
          ⟨l, mem_filter.mpr ⟨hl, hlT⟩⟩
        have hpi : part i = (((blk i).erase i).filter fun l => l ∉ T).min' hne := by
          change (if i ∈ V0 then (if h : (((blk i).erase i).filter fun l => l ∉ T).Nonempty then
            (((blk i).erase i).filter fun l => l ∉ T).min' h else i) else pd i) = _
          rw [if_pos hiV, dif_pos hne]
        have hm := min'_mem _ hne
        rw [← hpi, mem_filter] at hm
        exact ⟨(hleaves i hi hiV _ hm.1).1, hiT, hm.2, fun _ => mem_of_mem_erase hm.1,
          fun h => absurd hiV h⟩
      · have hpi : part i = pd i := by simp only [part, hiV, if_false]
        rw [hpi]
        have hadj := hpd i hi
        have hpp := hlone i hi hiV _ hadj
        refine ⟨hadj, hiT, ?_, fun h => absurd h hiV, fun _ => rfl⟩
        intro h
        exact hiT ((pend_mem_iff hπ hpp (dadj_symm hadj)).mp h)
    -- the vertices of the edge of a chosen block
    have hsep : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → ∀ a, (a = i ∨ a = part i) →
        ∀ b, (b = j ∨ b = part j) → a ≠ b := by
      have hloc : ∀ i ∈ C, ∀ a, (a = i ∨ a = part i) → a ∈ blk i ∨ (i ∉ V0 ∧ a = pd i) := by
        intro i hiC a ha
        have hi := (mem_filter.mp hiC).1
        obtain ⟨-, -, -, h4, h5⟩ := hpart i hiC
        rcases ha with rfl | rfl
        · exact Or.inl (hself a hi)
        · by_cases hiV : i ∈ V0
          · exact Or.inl (h4 hiV)
          · exact Or.inr ⟨hiV, h5 hiV⟩
      intro i hiC j hjC hij a ha b hb hab
      have hi := (mem_filter.mp hiC).1
      have hj := (mem_filter.mp hjC).1
      subst hab
      rcases hloc i hiC a ha with h1 | ⟨hiV, h1⟩ <;> rcases hloc j hjC a hb with h2 | ⟨hjV, h2⟩
      · exact disjoint_left.mp (hdisj i hi j hj hij) h1 h2
      · have hpp : IsPend D a := by rw [h2]; exact hlone j hj hjV _ (hpd j hj)
        exact (mem_filter.mp (hblkΦ i hi h1)).2.1 hpp
      · have hpp : IsPend D a := by rw [h1]; exact hlone i hi hiV _ (hpd i hi)
        exact (mem_filter.mp (hblkΦ j hj h2)).2.1 hpp
      · have hpp : IsPend D a := by rw [h1]; exact hlone i hi hiV _ (hpd i hi)
        have hai : DAdj D a i := by rw [h1]; exact dadj_symm (hpd i hi)
        have haj : DAdj D a j := by rw [h2]; exact dadj_symm (hpd j hj)
        exact hij (eq_of_pend hpp hai haj).symm
    set P0 := C.image fun i => ord2 i (part i)
    have hP0card : P0.card = C.card := by
      apply card_image_of_injOn
      intro i hi j hj he
      by_contra hij
      have hc := ord2_cases i (part i)
      have hc' := ord2_cases j (part j)
      simp only at he
      rw [he] at hc
      exact hsep i hi j hj hij _ hc.1 _ hc'.1 rfl
    have hP0sub : P0 ⊆ D.M := by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
      exact ord2_mem hlt (hpart i hi).1
    have hP0disj : VDisj P0 := by
      intro m hm m' hm' hmm'
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hm'
      have hij : i ≠ j := fun h => hmm' (by rw [h])
      have hc := ord2_cases i (part i)
      have hc' := ord2_cases j (part j)
      exact ⟨hsep i hi j hj hij _ hc.1 _ hc'.1, hsep i hi j hj hij _ hc.1 _ hc'.2,
        hsep i hi j hj hij _ hc.2 _ hc'.1, hsep i hi j hj hij _ hc.2 _ hc'.2⟩
    have hP0out : ∀ m ∈ P0, m.1 ∉ T ∧ m.2 ∉ T := by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
      obtain ⟨-, h2, h3, -, -⟩ := hpart i hi
      have hc := ord2_cases i (part i)
      refine ⟨?_, ?_⟩
      · rcases hc.1 with h | h <;> rw [h] <;> assumption
      · rcases hc.2 with h | h <;> rw [h] <;> assumption
    have hc := card_balanced_fiber_of_matching D hlt hleaf hTk P0 hP0sub hP0disj hP0out
    rw [hP0card] at hc
    exact hc
  -- summing over the tie sets
  set b : ℝ := 2 * Δ + 2 with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hyb : y * b = 1 := by rw [hy, hb]; field_simp
  have hcover : Pass ⊆ 𝒯.biUnion fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k) := by
    intro π hπ
    refine mem_biUnion.mpr ⟨tieSet k π, mem_image_of_mem _ hπ, ?_⟩
    simp only [fiber, mem_filter, mem_univ, true_and]
    exact (mem_filter.mp hπ).2.1
  have hstep1 : (Pass.card : ℝ) ≤ ∑ T in 𝒯, (F : ℝ) * (1 / 2 : ℝ) ^ μ (T ∩ Φ) := by
    have h1 : Pass.card ≤ ∑ T in 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card :=
      (card_le_of_subset hcover).trans card_biUnion_le
    have h1' : (Pass.card : ℝ) ≤
        ∑ T in 𝒯, (((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card : ℝ) := by
      exact_mod_cast h1
    refine h1'.trans (sum_le_sum fun T hT => ?_)
    have h := hper T hT
    have h' : (((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card : ℝ) *
        2 ^ μ (T ∩ Φ) ≤ F := by exact_mod_cast h
    have hpos : (0 : ℝ) < 2 ^ μ (T ∩ Φ) := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff hpos]
    exact h'
  -- each term is at most `b^k y^{|T ∩ Φ|} 2^{-μ}`
  have hstep2 : ∀ T ∈ 𝒯, (1 / 2 : ℝ) ^ μ (T ∩ Φ) ≤
      b ^ k * (y ^ (T ∩ Φ).card * (1 / 2 : ℝ) ^ μ (T ∩ Φ)) := by
    intro T hT
    obtain ⟨π, -, rfl⟩ := mem_image.mp hT
    have hcard : (tieSet k π ∩ Φ).card ≤ k :=
      (card_le_of_subset (inter_subset_left _ _)).trans (card_tieSet hk π).le
    have hyk : y ^ k ≤ y ^ (tieSet k π ∩ Φ).card := pow_le_pow_of_le_one hy0.le hy1 hcard
    have hbyk : b ^ k * y ^ k = 1 := by rw [← mul_pow, mul_comm, hyb, one_pow]
    have h12 : (0 : ℝ) ≤ (1 / 2) ^ μ (tieSet k π ∩ Φ) := by positivity
    calc (1 / 2 : ℝ) ^ μ (tieSet k π ∩ Φ) = b ^ k * y ^ k * (1 / 2 : ℝ) ^ μ (tieSet k π ∩ Φ) := by
          rw [hbyk, one_mul]
      _ ≤ b ^ k * y ^ (tieSet k π ∩ Φ).card * (1 / 2 : ℝ) ^ μ (tieSet k π ∩ Φ) := by
          apply mul_le_mul_of_nonneg_right _ h12
          exact mul_le_mul_of_nonneg_left hyk (by positivity)
      _ = _ := by ring
  have hinj : Set.InjOn (fun T => T ∩ Φ) 𝒯 := by
    intro T hT T' hT' he
    obtain ⟨π, hπ, rfl⟩ := mem_image.mp (mem_coe.mp hT)
    obtain ⟨π', hπ', rfl⟩ := mem_image.mp (mem_coe.mp hT')
    exact tie_eq_of_inter hlt (mem_filter.mp hπ).2 (mem_filter.mp hπ').2 he
  have hstep3 : ∑ T in 𝒯, y ^ (T ∩ Φ).card * (1 / 2 : ℝ) ^ μ (T ∩ Φ) ≤ 1 := by
    rw [← sum_image (f := fun A => y ^ A.card * (1 / 2 : ℝ) ^ μ A) hinj]
    have hsub : 𝒯.image (fun T => T ∩ Φ) ⊆ Φ.powerset := by
      intro A hA
      obtain ⟨T, -, rfl⟩ := mem_image.mp hA
      exact mem_powerset.mpr (inter_subset_right _ _)
    calc ∑ A in 𝒯.image (fun T => T ∩ Φ), y ^ A.card * (1 / 2 : ℝ) ^ μ A
        ≤ ∑ A in Φ.powerset, y ^ A.card * (1 / 2 : ℝ) ^ μ A :=
          sum_le_sum_of_subset_of_nonneg hsub fun A _ _ => by positivity
      _ = ∑ A in (I.biUnion blk).powerset, ∏ i in I, g i (A ∩ blk i) := by
          rw [hunion]
          exact sum_congr rfl fun A hA => (hfact A (mem_powerset.mp hA)).symm
      _ = ∏ i in I, ∑ S in (blk i).powerset, g i S := sum_powerset_biUnion I blk hdisj g
      _ ≤ ∏ _i in I, (1 : ℝ) := by
          apply prod_le_prod
          · intro i _
            apply sum_nonneg
            intro S _
            simp only [hg]
            positivity
          · exact hblock
      _ = 1 := prod_const_one
  calc ((univ.filter (DPasses D k)).card : ℝ) = (Pass.card : ℝ) := rfl
    _ ≤ ∑ T in 𝒯, (F : ℝ) * (1 / 2 : ℝ) ^ μ (T ∩ Φ) := hstep1
    _ ≤ ∑ T in 𝒯, (F : ℝ) * (b ^ k * (y ^ (T ∩ Φ).card * (1 / 2 : ℝ) ^ μ (T ∩ Φ))) :=
        sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (hstep2 T hT) (Nat.cast_nonneg _)
    _ = (F : ℝ) * b ^ k * ∑ T in 𝒯, y ^ (T ∩ Φ).card * (1 / 2 : ℝ) ^ μ (T ∩ Φ) := by
        rw [mul_sum]; refine sum_congr rfl fun T _ => ?_; ring
    _ ≤ (F : ℝ) * b ^ k * 1 := mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = (F : ℝ) * b ^ k := mul_one _

end Reduced

end MaxCaterpillar.Simplify
