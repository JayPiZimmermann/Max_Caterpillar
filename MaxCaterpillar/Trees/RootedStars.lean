import MaxCaterpillar.CountExp.Main

/-!
# The exponential count survives the rooted stars of Brunck et al.

The vocabulary of Brunck–Hertrich–Rueß–Stade–Yehudayoff ("Two ReLU layers is all
you need", Sec. 7.1) consists of pyramids over the parallelepipeds `B_{v,π,M}`.
For `M ≠ ∅` these are the caterpillar polytopes; for `M = ∅` the pyramid depends
only on the apex `a = v` and the root `c = π₁`, and its support function is the
*rooted star*
`S_{a,c}(y) = σ(y_c - y_a + ∑_{l ≠ a, c} σ(y_c - y_l))`.
Faces of a rooted-star pyramid that omit a leaf edge are caterpillar face functions
(checked exactly for `N ≤ 6` by `research/sN/trees/star_faces_check.py`); the faces that
keep every leaf edge (linearly or as a hinge) are covered here as `rootedStarFace`.

On every `k`-locality with `3 ≤ k ≤ N - 1` the mixed difference kills every rooted
star and every such face: if the root `c` is tied, some coordinate below the tie makes the
preactivation positive on the whole box, and the star equals a sum of functions of
at most two coordinates; if `c` is not tied, every tied leaf term vanishes and the
star does not depend on a tied coordinate other than `a`.  Hence the counting of
`CountExp` applies to the caterpillar units alone:
`C(N, k) ≤ 6^k |K|` for `3 ≤ k ≤ N - 1`, however many rooted stars are added.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountExp CountCubic

/-- The rooted star with apex `a` and root `c`:
`S_{a,c}(y) = σ(y_c - y_a + ∑_{l ∉ {a, c}} σ(y_c - y_l))`. -/
noncomputable def rootedStar {N : ℕ} (a c : Fin N) (y : Fin N → ℝ) : ℝ :=
  MaxNN.relu (y c - y a + ∑ l in (univ.erase a).erase c, MaxNN.relu (y c - y l))

/-! ## The box (local copies of the private lemmas of `CountExp.W1Functional`) -/

section Box

variable {N : ℕ} {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

theorem mem_tieSet' {o : Fin N} : o ∈ tieSet k π ↔ ((π o : Fin N) : ℕ) < k := by
  unfold tieSet
  rw [mem_filter]
  exact and_iff_right (mem_univ o)

theorem basePtR_of_mem' {o : Fin N} (ho : o ∈ tieSet k π) : basePtR k B π o = 0 := by
  unfold basePtR basePt
  rw [if_pos (mem_tieSet'.mp ho)]
  norm_num

theorem basePtR_le_neg_one' (hB : 1 ≤ B) {o : Fin N} (ho : o ∉ tieSet k π) :
    basePtR k B π o ≤ -1 := by
  unfold basePtR basePt
  rw [if_neg (fun h => ho (mem_tieSet'.mpr h))]
  push_cast
  have : (1 : ℝ) ≤ (B : ℝ) ^ ((π o : Fin N) : ℕ) :=
    one_le_pow_of_one_le (by exact_mod_cast hB) _
  linarith

theorem basePtR_nonpos' (o : Fin N) : basePtR k B π o ≤ 0 := by
  unfold basePtR basePt
  split_ifs
  · norm_num
  · push_cast
    have : (0 : ℝ) ≤ (B : ℝ) ^ ((π o : Fin N) : ℕ) := by positivity
    linarith

theorem boxPt_of_mem' {S : Finset (Fin N)} {o : Fin N} (ho : o ∈ tieSet k π) :
    boxPt k B δ π S o = if o ∈ S then δ else 0 := by
  unfold boxPt
  rw [basePtR_of_mem' ho, zero_add]

theorem boxPt_of_not_mem' {S : Finset (Fin N)} (hS : S ⊆ tieSet k π) {o : Fin N}
    (ho : o ∉ tieSet k π) : boxPt k B δ π S o = basePtR k B π o := by
  unfold boxPt
  rw [if_neg (fun h => ho (hS h)), add_zero]

theorem boxPt_le' (S : Finset (Fin N)) (o : Fin N) :
    boxPt k B δ π S o ≤ if o ∈ S then δ else 0 := by
  unfold boxPt
  linarith [basePtR_nonpos' (k := k) (B := B) (π := π) o]

theorem boxPt_insert_of_ne' {S : Finset (Fin N)} {t o : Fin N} (hot : o ≠ t) :
    boxPt k B δ π (insert t S) o = boxPt k B δ π S o := by
  unfold boxPt
  by_cases ho : o ∈ S
  · rw [if_pos (mem_insert_of_mem ho), if_pos ho]
  · rw [if_neg ho, if_neg (fun h => (mem_insert.mp h).elim hot ho)]

theorem mixedDiff_congr' {g g' : (Fin N → ℝ) → ℝ}
    (h : ∀ S ⊆ tieSet k π, g (boxPt k B δ π S) = g' (boxPt k B δ π S)) :
    mixedDiff k B δ π g = mixedDiff k B δ π g' := by
  rw [mixedDiff_apply, mixedDiff_apply]
  exact sum_congr rfl fun S hS => by rw [h S (mem_powerset.mp hS)]

theorem mixedDiff_eq_zero_of_insert' {g : (Fin N → ℝ) → ℝ} {t : Fin N}
    (ht : t ∈ tieSet k π)
    (h : ∀ S ⊆ tieSet k π, t ∉ S → g (boxPt k B δ π (insert t S)) = g (boxPt k B δ π S)) :
    mixedDiff k B δ π g = 0 := by
  rw [mixedDiff_apply]
  have hTe : tieSet k π = insert t ((tieSet k π).erase t) := (insert_erase ht).symm
  have hnot : t ∉ (tieSet k π).erase t := not_mem_erase t _
  rw [hTe, sum_powerset_insert hnot, ← sum_add_distrib]
  refine sum_eq_zero fun S hS => ?_
  have hS' : S ⊆ (tieSet k π).erase t := mem_powerset.mp hS
  have htS : t ∉ S := fun h => hnot (hS' h)
  have h1 : (insert t ((tieSet k π).erase t) \ S).card = ((tieSet k π).erase t \ S).card + 1 := by
    rw [insert_sdiff_of_not_mem _ htS,
      card_insert_of_not_mem (fun h => hnot (mem_sdiff.mp h).1)]
  have h2 : insert t ((tieSet k π).erase t) \ insert t S = (tieSet k π).erase t \ S := by
    rw [insert_sdiff_insert, sdiff_insert_of_not_mem hnot]
  rw [h1, h2, h S (hS'.trans (erase_subset t _)) htS, pow_succ]
  ring

/-- A tie coordinate different from two given coordinates (`k ≥ 3`). -/
theorem exists_tie_ne (hk : 3 ≤ k) (hkN : k ≤ N) (i j : Fin N) :
    ∃ t ∈ tieSet k π, t ≠ i ∧ t ≠ j := by
  by_contra hcon
  push_neg at hcon
  have hsub : tieSet k π ⊆ {i, j} := fun t ht => by
    by_cases hti : t = i
    · rw [hti]; exact mem_insert_self _ _
    · rw [hcon t ht hti]; exact mem_insert_of_mem (mem_singleton_self _)
  have h1 := card_le_of_subset hsub
  have h2 := card_insert_le i ({j} : Finset (Fin N))
  rw [card_singleton] at h2
  rw [card_tieSet hkN π] at h1
  omega

theorem mixedDiff_eq_zero_of_two' (hk : 3 ≤ k) (hkN : k ≤ N) {g : (Fin N → ℝ) → ℝ}
    (i j : Fin N) (hg : ∀ x x' : Fin N → ℝ, x i = x' i → x j = x' j → g x = g x') :
    mixedDiff k B δ π g = 0 := by
  obtain ⟨t, htT, hti, htj⟩ := exists_tie_ne (π := π) hk hkN i j
  refine mixedDiff_eq_zero_of_insert' htT fun S _ _ => hg _ _ ?_ ?_
  · exact boxPt_insert_of_ne' (Ne.symm hti)
  · exact boxPt_insert_of_ne' (Ne.symm htj)

end Box

/-! ## The mixed difference kills every rooted star below the full tie -/

theorem mixedDiff_rootedStar {N k B : ℕ} {δ : ℝ} (π : Equiv.Perm (Fin N))
    (hk : 3 ≤ k) (hkN : k < N) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (a c : Fin N) :
    mixedDiff k B δ π (rootedStar a c) = 0 := by
  classical
  set T := tieSet k π with hTdef
  set L := (univ.erase a).erase c with hL
  by_cases hc : c ∈ T
  · -- some coordinate lies below the tie
    obtain ⟨o, ho⟩ : ∃ o, o ∉ T := by
      by_contra hcon
      push_neg at hcon
      have h1 : (univ : Finset (Fin N)) ⊆ T := fun x _ => hcon x
      have h2 := card_le_of_subset h1
      rw [card_univ, Fintype.card_fin, hTdef, card_tieSet hkN.le π] at h2
      omega
    -- the preactivation is nonnegative on the box
    have hpos : ∀ S ⊆ T, 0 ≤ boxPt k B δ π S c - boxPt k B δ π S a +
        ∑ l in L, MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S l) := by
      intro S hS
      have hxc : 0 ≤ boxPt k B δ π S c := by
        rw [boxPt_of_mem' hc]
        split_ifs
        · exact hδ
        · exact le_rfl
      have hxa : boxPt k B δ π S a ≤ δ := by
        refine (boxPt_le' S a).trans ?_
        split_ifs
        · exact le_rfl
        · exact hδ
      have hsum0 : 0 ≤ ∑ l in L, MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S l) :=
        sum_nonneg fun l _ => relu_nonneg _
      by_cases hoa : o = a
      · have : boxPt k B δ π S a ≤ -1 := by
          rw [← hoa, boxPt_of_not_mem' hS ho]
          exact basePtR_le_neg_one' hB ho
        linarith
      · have hoc : o ≠ c := fun h => ho (h ▸ hc)
        have hoL : o ∈ L := by
          rw [hL]
          exact mem_erase.mpr ⟨hoc, mem_erase.mpr ⟨hoa, mem_univ _⟩⟩
        have hxo : boxPt k B δ π S o ≤ -1 := by
          rw [boxPt_of_not_mem' hS ho]
          exact basePtR_le_neg_one' hB ho
        have h1 : MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S o) ≤
            ∑ l in L, MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S l) :=
          single_le_sum (f := fun l => MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S l))
            (fun l _ => relu_nonneg _) hoL
        have h2 : boxPt k B δ π S c - boxPt k B δ π S o ≤
            MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S o) := le_max_right _ _
        linarith
    -- on the box the star equals its preactivation, a sum of two-coordinate terms
    have heq : mixedDiff k B δ π (rootedStar a c) = mixedDiff k B δ π
        ((fun y => y c - y a) + ∑ l in L, fun y => MaxNN.relu (y c - y l)) := by
      refine mixedDiff_congr' fun S hS => ?_
      unfold rootedStar
      rw [relu_of_nonneg (hpos S hS), Pi.add_apply, Finset.sum_apply]
    rw [heq, map_add, map_sum]
    have h1 : mixedDiff k B δ π (fun y : Fin N → ℝ => y c - y a) = 0 :=
      mixedDiff_eq_zero_of_two' hk hkN.le c a fun x x' h1 h2 => by simp only [h1, h2]
    rw [h1, zero_add]
    exact sum_eq_zero fun l _ =>
      mixedDiff_eq_zero_of_two' hk hkN.le c l fun x x' h1 h2 => by simp only [h1, h2]
  · -- the root is below the tie: no tied leaf term contributes
    obtain ⟨t, htT, hta, htc⟩ := exists_tie_ne (π := π) hk hkN.le a c
    refine mixedDiff_eq_zero_of_insert' htT fun S hS _ => ?_
    have hval : ∀ S' ⊆ T, rootedStar a c (boxPt k B δ π S') =
        MaxNN.relu (boxPt k B δ π S' c - boxPt k B δ π S' a +
          ∑ l in L.filter (fun l => l ∉ T),
            MaxNN.relu (boxPt k B δ π S' c - boxPt k B δ π S' l)) := by
      intro S' hS'
      unfold rootedStar
      congr 2
      rw [sum_filter]
      refine sum_congr rfl fun l _ => ?_
      by_cases hl : l ∈ T
      · rw [if_neg (not_not.mpr hl)]
        apply relu_of_nonpos
        have hxc : boxPt k B δ π S' c ≤ -1 := by
          rw [boxPt_of_not_mem' hS' hc]
          exact basePtR_le_neg_one' hB hc
        have hxl : 0 ≤ boxPt k B δ π S' l := by
          rw [boxPt_of_mem' hl]
          split_ifs
          · exact hδ
          · exact le_rfl
        linarith
      · rw [if_pos hl]
    have hS2 : insert t S ⊆ T := insert_subset_iff.mpr ⟨htT, hS⟩
    rw [hval _ hS2, hval _ hS, boxPt_insert_of_ne' htc.symm, boxPt_insert_of_ne' hta.symm]
    congr 2
    refine sum_congr rfl fun l hl => ?_
    have hlT : l ∉ T := (mem_filter.mp hl).2
    have hlt : l ≠ t := fun h => hlT (h ▸ htT)
    rw [boxPt_insert_of_ne' hlt]

/-! ## Faces of the rooted-star pyramids

A face of the rooted-star pyramid keeps every leaf edge linear, as a hinge, or omits
it.  Faces that omit a leaf edge are caterpillar face functions
(`research/sN/trees/star_faces_check.py`, exact for `N ≤ 6`); the remaining faces keep
every leaf edge, linearly for `l ∈ Lin` and as a hinge otherwise:
`S_{a,c,Lin}(y) = σ(y_c - y_a + ∑_{l ∉ {a,c}} (l ∈ Lin ? y_c - y_l : σ(y_c - y_l)))`.
`Lin = ∅` is the rooted star itself. -/

/-- The preactivation of the face `(a, c, Lin)` of the rooted-star pyramid. -/
noncomputable def starFaceArg {N : ℕ} (a c : Fin N) (Lin : Finset (Fin N)) (y : Fin N → ℝ) : ℝ :=
  y c - y a + ∑ l in (univ.erase a).erase c,
    (if l ∈ Lin then y c - y l else MaxNN.relu (y c - y l))

/-- The face function `S_{a,c,Lin} = σ(starFaceArg a c Lin)`. -/
noncomputable def rootedStarFace {N : ℕ} (a c : Fin N) (Lin : Finset (Fin N))
    (y : Fin N → ℝ) : ℝ :=
  MaxNN.relu (starFaceArg a c Lin y)

theorem rootedStarFace_empty {N : ℕ} (a c : Fin N) :
    rootedStarFace a c ∅ = rootedStar a c := by
  funext y
  unfold rootedStarFace starFaceArg rootedStar
  simp only [not_mem_empty, if_false]

theorem mixedDiff_rootedStarFace {N k B : ℕ} {δ : ℝ} (π : Equiv.Perm (Fin N))
    (hk : 3 ≤ k) (hkN : k < N) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδN : δ * (N + 1) ≤ 1)
    (a c : Fin N) (Lin : Finset (Fin N)) :
    mixedDiff k B δ π (rootedStarFace a c Lin) = 0 := by
  classical
  set T := tieSet k π with hTdef
  set L := (univ.erase a).erase c with hL
  have hcardL : (L.card : ℝ) ≤ N := by
    have := card_le_univ L
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hle : ∀ S : Finset (Fin N), ∀ o, boxPt k B δ π S o ≤ δ := fun S o =>
    (boxPt_le' S o).trans (by split_ifs; exacts [le_rfl, hδ])
  have hdiff : ∀ S : Finset (Fin N), ∀ o,
      boxPt k B δ π S o - basePtR k B π o = if o ∈ S then δ else 0 := fun S o => by
    unfold boxPt; ring
  by_cases hc : c ∈ T
  · obtain ⟨o, ho⟩ : ∃ o, o ∉ T := by
      by_contra hcon
      push_neg at hcon
      have h1 : (univ : Finset (Fin N)) ⊆ T := fun x _ => hcon x
      have h2 := card_le_of_subset h1
      rw [card_univ, Fintype.card_fin, hTdef, card_tieSet hkN.le π] at h2
      omega
    have hpos : ∀ S ⊆ T, 0 ≤ starFaceArg a c Lin (boxPt k B δ π S) := by
      intro S hS
      set x := boxPt k B δ π S
      have hxc : 0 ≤ x c := by
        show 0 ≤ boxPt k B δ π S c
        rw [boxPt_of_mem' hc]
        split_ifs
        · exact hδ
        · exact le_rfl
      have hxo : x o ≤ -1 := by
        show boxPt k B δ π S o ≤ -1
        rw [boxPt_of_not_mem' hS ho]
        exact basePtR_le_neg_one' hB ho
      have hterm : ∀ l, x c - x l ≤
          (if l ∈ Lin then x c - x l else MaxNN.relu (x c - x l)) := fun l => by
        split_ifs
        · exact le_rfl
        · exact le_max_right _ _
      have hterm' : ∀ l, -δ ≤ (if l ∈ Lin then x c - x l else MaxNN.relu (x c - x l)) :=
        fun l => by linarith [hterm l, hle S l]
      have hlow : ∀ s : Finset (Fin N), -(δ * s.card) ≤
          ∑ l in s, (if l ∈ Lin then x c - x l else MaxNN.relu (x c - x l)) := fun s => by
        have := Finset.sum_le_sum (s := s) fun l (_ : l ∈ s) => hterm' l
        rw [sum_const, nsmul_eq_mul] at this
        linarith
      unfold starFaceArg
      by_cases hoa : o = a
      · have hxa : x a ≤ -1 := hoa ▸ hxo
        have := hlow L
        have h2 : δ * (L.card : ℝ) ≤ δ * N := mul_le_mul_of_nonneg_left hcardL hδ
        nlinarith
      · have hoc : o ≠ c := fun h => ho (h ▸ hc)
        have hoL : o ∈ L := by
          rw [hL]
          exact mem_erase.mpr ⟨hoc, mem_erase.mpr ⟨hoa, mem_univ _⟩⟩
        rw [← add_sum_erase L _ hoL]
        have h1 := hterm o
        have h2 := hlow (L.erase o)
        have h3 : ((L.erase o).card : ℝ) ≤ N := by
          have := card_le_univ (L.erase o)
          rw [Fintype.card_fin] at this
          exact_mod_cast this
        have h4 : δ * ((L.erase o).card : ℝ) ≤ δ * N := mul_le_mul_of_nonneg_left h3 hδ
        have h5 := hle S a
        nlinarith
    have heq : mixedDiff k B δ π (rootedStarFace a c Lin) = mixedDiff k B δ π
        ((fun y => y c - y a) + ∑ l in L,
          fun y => (if l ∈ Lin then y c - y l else MaxNN.relu (y c - y l))) := by
      refine mixedDiff_congr' fun S hS => ?_
      unfold rootedStarFace
      rw [relu_of_nonneg (hpos S hS), Pi.add_apply, Finset.sum_apply]
      rfl
    rw [heq, map_add, map_sum]
    have h1 : mixedDiff k B δ π (fun y : Fin N → ℝ => y c - y a) = 0 :=
      mixedDiff_eq_zero_of_two' hk hkN.le c a fun x x' h1 h2 => by simp only [h1, h2]
    rw [h1, zero_add]
    exact sum_eq_zero fun l _ =>
      mixedDiff_eq_zero_of_two' hk hkN.le c l fun x x' h1 h2 => by simp only [h1, h2]
  · -- the root is below the tie
    set base := basePtR k B π with hbase
    set A0 := starFaceArg a c Lin base with hA0
    have hcb : base c ≤ -1 := basePtR_le_neg_one' hB hc
    have hint : ∃ z : ℤ, A0 = z := by
      have hb : ∀ o, ∃ z : ℤ, base o = z := fun o => ⟨basePt k B π o, rfl⟩
      have hr : ∀ z : ℤ, ∃ w : ℤ, MaxNN.relu (z : ℝ) = w := fun z =>
        ⟨max 0 z, by unfold MaxNN.relu; push_cast; rfl⟩
      have hs : ∀ l, ∃ w : ℤ,
          (if l ∈ Lin then base c - base l else MaxNN.relu (base c - base l)) = w := by
        intro l
        obtain ⟨zc, hzc⟩ := hb c
        obtain ⟨zl, hzl⟩ := hb l
        split_ifs
        · exact ⟨zc - zl, by rw [hzc, hzl]; push_cast; ring⟩
        · obtain ⟨w, hw⟩ := hr (zc - zl)
          exact ⟨w, by rw [hzc, hzl, ← hw]; push_cast; ring_nf⟩
      choose w hw using hs
      obtain ⟨zc, hzc⟩ := hb c
      obtain ⟨za, hza⟩ := hb a
      refine ⟨zc - za + ∑ l in L, w l, ?_⟩
      rw [hA0]
      unfold starFaceArg
      rw [hzc, hza]
      push_cast
      congr 1
      refine sum_congr rfl fun l _ => ?_
      rw [← hw l, hzc]
    obtain ⟨z, hz⟩ := hint
    -- the preactivation on the box
    have hkey : ∀ S ⊆ T, starFaceArg a c Lin (boxPt k B δ π S) =
        A0 - (boxPt k B δ π S a - base a) -
          ∑ l in L, (if l ∈ Lin then boxPt k B δ π S l - base l else 0) := by
      intro S hS
      have hxc : boxPt k B δ π S c = base c := boxPt_of_not_mem' hS hc
      have ht : ∀ l, (if l ∈ Lin then boxPt k B δ π S c - boxPt k B δ π S l
            else MaxNN.relu (boxPt k B δ π S c - boxPt k B δ π S l)) =
          (if l ∈ Lin then base c - base l else MaxNN.relu (base c - base l)) -
            (if l ∈ Lin then boxPt k B δ π S l - base l else 0) := by
        intro l
        rw [hxc]
        split_ifs with hl
        · ring
        · rw [sub_zero]
          by_cases hlT : l ∈ T
          · have h1 : 0 ≤ boxPt k B δ π S l := by
              rw [boxPt_of_mem' hlT]; split_ifs; exacts [hδ, le_rfl]
            have h2 : base l = 0 := basePtR_of_mem' hlT
            rw [relu_of_nonpos (by linarith), relu_of_nonpos (by linarith)]
          · rw [boxPt_of_not_mem' hS hlT]
      rw [hA0]
      unfold starFaceArg
      rw [sum_congr rfl fun l _ => ht l, sum_sub_distrib, hxc]
      ring
    have hnn : ∀ S : Finset (Fin N), ∀ o, 0 ≤ boxPt k B δ π S o - base o ∧
        boxPt k B δ π S o - base o ≤ δ := fun S o => by
      rw [hbase, hdiff S o]; split_ifs; exacts [⟨hδ, le_rfl⟩, ⟨le_rfl, hδ⟩]
    have hsum : ∀ S : Finset (Fin N), 0 ≤
        ∑ l in L, (if l ∈ Lin then boxPt k B δ π S l - base l else 0) ∧
        ∑ l in L, (if l ∈ Lin then boxPt k B δ π S l - base l else 0) ≤ δ * N := by
      intro S
      constructor
      · exact sum_nonneg fun l _ => by split_ifs; exacts [(hnn S l).1, le_rfl]
      · have h := Finset.sum_le_sum (s := L) fun l (_ : l ∈ L) =>
          (show (if l ∈ Lin then boxPt k B δ π S l - base l else 0) ≤ δ by
            split_ifs; exacts [(hnn S l).2, hδ])
        rw [sum_const, nsmul_eq_mul] at h
        nlinarith [mul_le_mul_of_nonneg_left hcardL hδ]
    rcases le_or_lt z 0 with hz0 | hz0
    · -- the face function vanishes on the box
      rw [mixedDiff_congr' (g' := 0) fun S hS => ?_, map_zero]
      unfold rootedStarFace
      rw [hkey S hS, Pi.zero_apply]
      apply relu_of_nonpos
      have : (z : ℝ) ≤ 0 := by exact_mod_cast hz0
      linarith [(hnn S a).1, (hsum S).1]
    · -- the face function is affine on the box
      have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz0
      rw [mixedDiff_congr' (g' := (fun _ => A0 + base a) - (fun y => y a) -
          ∑ l in L, fun y => (if l ∈ Lin then y l - base l else 0)) fun S hS => ?_]
      · rw [map_sub, map_sub, map_sum]
        have h1 : mixedDiff k B δ π (fun _ : Fin N → ℝ => A0 + base a) = 0 :=
          mixedDiff_eq_zero_of_two' hk hkN.le a a fun _ _ _ _ => rfl
        have h2 : mixedDiff k B δ π (fun y : Fin N → ℝ => y a) = 0 :=
          mixedDiff_eq_zero_of_two' hk hkN.le a a fun x x' h _ => h
        have h3 : ∑ l in L, mixedDiff k B δ π
            (fun y : Fin N → ℝ => (if l ∈ Lin then y l - base l else 0)) = 0 :=
          sum_eq_zero fun l _ =>
            mixedDiff_eq_zero_of_two' hk hkN.le l l fun x x' h _ => by simp only [h]
        rw [h1, h2, h3]
        ring
      · unfold rootedStarFace
        rw [hkey S hS, relu_of_nonneg]
        · simp only [Pi.sub_apply, Finset.sum_apply]
          ring
        · have h1 := (hnn S a).2
          have h2 := (hsum S).2
          have : δ + δ * N ≤ 1 := by linarith
          linarith

/-! ## Every locality below the full tie is passed by a caterpillar unit -/

theorem exists_passes_rootedStar (r : ℕ) (K : Finset (RealKey (r + 1)))
    (hK : K ⊆ normalizedKeys r) (d : RealKey (r + 1) → ℝ)
    (e : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x +
      ∑ p : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)),
        e p * rootedStarFace p.1 p.2.1 p.2.2 x +
        auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k < r + 1 + 1) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ key ∈ K, Passes key k π := by
  classical
  set c : RealKey (r + 1) → ℝ :=
    fun key => ∑ o, |keyHead key o| + 2 * ((pairSet key).card : ℝ) with hc
  have hc0 : ∀ key, 0 ≤ c key := fun key =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _)
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))
  set C : ℝ := ∑ key in K, c key
  have hcC : ∀ key ∈ K, c key ≤ C := fun key hkey =>
    Finset.single_le_sum (fun key _ => hc0 key) hkey
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun key _ => hc0 key
  set δ : ℝ := 1 / (C + ((r + 1 + 1 : ℕ) : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδN : δ * (((r + 1 + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [hδ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  set B : ℕ := ⌈C⌉₊ + 1 with hB
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have hCB : C < B := by
    rw [hB]
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil C) (lt_add_one _)
  have hfun : Maximum (r + 1 + 1) = (∑ key in K, d key • realUnitY key) +
      (∑ p : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)),
        e p • rootedStarFace p.1 p.2.1 p.2.2) +
        auxiliary a := by
    funext x
    rw [h x, Pi.add_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    rfl
  have hval := congrArg (mixedDiff k B δ π) hfun
  have hstar : mixedDiff k B δ π
      (∑ p : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)),
        e p • rootedStarFace p.1 p.2.1 p.2.2) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [map_smul, mixedDiff_rootedStarFace π hk hkN hB1 hδ0.le hδN, smul_zero]
  rw [mixedDiff_maximum (le_trans (by norm_num) hk) hkN.le hB1 hδ0.le, map_add, map_add,
    mixedDiff_auxiliary hk hkN.le B δ π a, add_zero, hstar, add_zero, map_sum] at hval
  have hne : ∑ key in K, mixedDiff k B δ π (d key • realUnitY key) ≠ 0 := by
    rw [← hval]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hδ0.ne'
  obtain ⟨key, hkey, hkey0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [map_smul, smul_eq_mul] at hkey0
  have hU : mixedDiff k B δ π (realUnitY key) ≠ 0 := right_ne_zero_of_mul hkey0
  have hδb : δ * c key < 1 := by
    calc δ * c key ≤ δ * C := mul_le_mul_of_nonneg_left (hcC key hkey) hδ0.le
      _ < δ * (C + ((r + 1 + 1 : ℕ) : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (by have : (0 : ℝ) ≤ ((r + 1 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hδ0
      _ = 1 := by rw [hδ]; field_simp
  obtain ⟨h0, hact⟩ := pass_of_mixedDiff_unit_ne (hK hkey) hk hkN.le hB1 hδ0 hδb π hU
  have hBk : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) < B := by
    have : ∑ o, |keyHead key o| + ((pairSet key).card : ℝ) ≤ c key := by
      simp only [hc]
      have : (0 : ℝ) ≤ ((pairSet key).card : ℝ) := Nat.cast_nonneg _
      linarith
    linarith [hcC key hkey]
  exact ⟨key, hkey, balanced_of_realUnitArg_eq_zero (hK hkey) hBk π h0, hact⟩

/-- **Binomial count with rooted stars.** `C(N, k) ≤ 6^k |K|` for `3 ≤ k ≤ N - 1`,
where `K` is the set of caterpillar units; the rooted stars are not counted. -/
theorem choose_le_six_pow_mul_card_rootedStar (r : ℕ) (K : Finset (RealKey (r + 1)))
    (hK : K ⊆ normalizedKeys r) (d : RealKey (r + 1) → ℝ)
    (e : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x +
      ∑ p : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)),
        e p * rootedStarFace p.1 p.2.1 p.2.2 x +
        auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k < r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card := by
  classical
  have hkN' : k ≤ r + 1 + 1 := hkN.le
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆ K.biUnion fun key =>
      passSet key k := by
    intro π _
    obtain ⟨key, hkey, hp⟩ := exists_passes_rootedStar r K hK d e a h hk hkN π
    refine Finset.mem_biUnion.mpr ⟨key, hkey, ?_⟩
    unfold passSet
    convert Finset.mem_filter.mpr ⟨Finset.mem_univ π, hp⟩
  have h1 := Finset.card_le_of_subset hcover
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : (r + 1 + 1)! ≤ K.card * (k ! * (r + 1 + 1 - k)! * 6 ^ k) :=
    calc (r + 1 + 1)! ≤ (K.biUnion fun key => passSet key k).card := h1
      _ ≤ ∑ key in K, (passSet key k).card := Finset.card_biUnion_le
      _ ≤ ∑ _key in K, k ! * (r + 1 + 1 - k)! * 6 ^ k :=
          Finset.sum_le_sum fun key hkey => card_passSet_le (hK hkey) hkN'
      _ = K.card * (k ! * (r + 1 + 1 - k)! * 6 ^ k) := by
          rw [Finset.sum_const, smul_eq_mul]
  rw [← Nat.choose_mul_factorial_mul_factorial hkN'] at h2
  have hpos : 0 < k ! * (r + 1 + 1 - k)! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h3 : (r + 1 + 1).choose k * (k ! * (r + 1 + 1 - k)!) ≤
      6 ^ k * K.card * (k ! * (r + 1 + 1 - k)!) := by
    calc (r + 1 + 1).choose k * (k ! * (r + 1 + 1 - k)!)
        = (r + 1 + 1).choose k * k ! * (r + 1 + 1 - k)! := by ring
      _ ≤ K.card * (k ! * (r + 1 + 1 - k)! * 6 ^ k) := h2
      _ = 6 ^ k * K.card * (k ! * (r + 1 + 1 - k)!) := by ring
  exact le_of_mul_le_mul_right h3 hpos

/-- **Exponential count with rooted stars.** For `N = r + 2 ≥ 4`,
`7^N ≤ (N + 1) N² 6^N |K|`, i.e. `|K| ≥ (7/6)^N / ((N + 1) N²)`. -/
theorem seven_pow_le_rootedStar (r : ℕ) (hr : 2 ≤ r) (K : Finset (RealKey (r + 1)))
    (hK : K ⊆ normalizedKeys r) (d : RealKey (r + 1) → ℝ)
    (e : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * realUnitY k x +
      ∑ p : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)),
        e p * rootedStarFace p.1 p.2.1 p.2.2 x +
        auxiliary a x) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * (r + 1 + 1) ^ 2 * 6 ^ (r + 1 + 1) * K.card := by
  have hmain : ∀ k, 3 ≤ k → k < r + 1 + 1 → (r + 1 + 1).choose k ≤ 6 ^ k * K.card :=
    fun k hk hkN => choose_le_six_pow_mul_card_rootedStar r K hK d e a h hk hkN
  clear h
  set N := r + 1 + 1 with hN
  -- at least one caterpillar unit
  have h3 := hmain 3 (le_refl 3) (by omega)
  have hK1 : 1 ≤ K.card := by
    by_contra hc
    push_neg at hc
    have h0 : K.card = 0 := Nat.lt_one_iff.mp hc
    rw [h0, mul_zero] at h3
    have : 0 < N.choose 3 := Nat.choose_pos (by omega)
    omega
  have hterm : ∀ m ≤ N, N.choose m * 6 ^ (N - m) ≤ N ^ 2 * 6 ^ N * K.card := by
    intro m hm
    have h6 : 6 ^ (N - m) * 6 ^ m = 6 ^ N := by rw [← pow_add, Nat.sub_add_cancel hm]
    by_cases hmid : 3 ≤ m ∧ m < N
    · have hc := hmain m hmid.1 hmid.2
      have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc N.choose m * 6 ^ (N - m) ≤ 6 ^ m * K.card * 6 ^ (N - m) := Nat.mul_le_mul_right _ hc
        _ = 6 ^ N * K.card := by rw [← h6]; ring
        _ = 1 * (6 ^ N * K.card) := (one_mul _).symm
        _ ≤ N ^ 2 * (6 ^ N * K.card) := Nat.mul_le_mul_right _ hN2
        _ = N ^ 2 * 6 ^ N * K.card := by ring
    · have hch : N.choose m ≤ N ^ 2 := by
        push_neg at hmid
        rcases Nat.lt_or_ge m 3 with hm3 | hm3
        · interval_cases m
          · rw [Nat.choose_zero_right]; exact Nat.one_le_pow _ _ (by omega)
          · rw [Nat.choose_one_right, pow_two]; exact Nat.le_mul_of_pos_left (by omega)
          · rw [Nat.choose_two_right, pow_two]
            exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
        · have hmN : m = N := le_antisymm hm (hmid hm3)
          rw [hmN, Nat.choose_self]; exact Nat.one_le_pow _ _ (by omega)
      have hp : 6 ^ (N - m) ≤ 6 ^ N := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
      calc N.choose m * 6 ^ (N - m) ≤ N ^ 2 * 6 ^ N := Nat.mul_le_mul hch hp
        _ = N ^ 2 * 6 ^ N * 1 := (mul_one _).symm
        _ ≤ N ^ 2 * 6 ^ N * K.card := Nat.mul_le_mul_left _ hK1
  have hbin : 7 ^ N = ∑ m in range (N + 1), 1 ^ m * 6 ^ (N - m) * N.choose m := by
    rw [show (7 : ℕ) = 1 + 6 from rfl, add_pow]
    simp only [Nat.cast_id]
  rw [hbin]
  calc ∑ m in range (N + 1), 1 ^ m * 6 ^ (N - m) * N.choose m
      ≤ ∑ _m in range (N + 1), N ^ 2 * 6 ^ N * K.card := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        rw [one_pow, one_mul, mul_comm]
        exact hterm m hmN
    _ = (N + 1) * N ^ 2 * 6 ^ N * K.card := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-! ## Public statements -/

/-- `K` together with the rooted stars is an expansion of the maximum in the
vocabulary of Brunck et al.: `K` is a set of caterpillar face descriptions and
`max_N = Σ_{k ∈ K} d_k U_k + Σ_{a,c,Lin} e_{a,c,Lin} S_{a,c,Lin} + (auxiliary functions)`,
where `S_{a,c,∅}` is the rooted star and `S_{a,c,Lin}` its faces keeping every leaf edge.
Only the caterpillar units are counted by `K`; arbitrary coefficients are allowed on
all rooted stars and their faces (all triples `(a, c, Lin)`, `a = c` included). -/
def IsRootedStarExpansion (r : ℕ) (K : Finset (FaceKey r)) : Prop :=
  K ⊆ caterpillarDescriptions r ∧
    ∃ (d : FaceKey r → ℝ) (e : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)) → ℝ)
      (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in K, d k * caterpillarFunction k x +
          ∑ p : Fin (r + 1 + 1) × Fin (r + 1 + 1) × Finset (Fin (r + 1 + 1)),
        e p * rootedStarFace p.1 p.2.1 p.2.2 x +
            ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

/-- **Binomial count for the vocabulary with rooted stars.** -/
theorem rootedStar_expansion_choose_le (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsRootedStarExpansion r K) {k : ℕ} (hk : 3 ≤ k) (hkN : k < r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card := by
  obtain ⟨hsub, d, e, a, h⟩ := hK
  exact choose_le_six_pow_mul_card_rootedStar r K hsub d e a h hk hkN

/-- **Exponential count for the vocabulary with rooted stars.** For `N = r + 2 ≥ 4`,
`7^N ≤ (N + 1) N² 6^N |K|`. -/
theorem rootedStar_expansion_exponential (r : ℕ) (hr : 2 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsRootedStarExpansion r K) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * (r + 1 + 1) ^ 2 * 6 ^ (r + 1 + 1) * K.card := by
  obtain ⟨hsub, d, e, a, h⟩ := hK
  exact seven_pow_le_rootedStar r hr K hsub d e a h

end MaxCaterpillar.Trees
