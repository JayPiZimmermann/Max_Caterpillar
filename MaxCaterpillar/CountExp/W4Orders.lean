import MaxCaterpillar.CountExp.Defs
import MaxCaterpillar.CountCubic.ForestOrientation

/-!
# Orders with a prescribed tie set (worker W4)

Step 5 of the main route (`research/sN/NOTE.md`, "MAIN ROUTE"):

* `card_tieSet`, `card_fiber`: every tie set has `k` elements and is the tie set of
  exactly `k! (N - k)!` permutations;
* `HingeCat.orient_eq_of_balanced`: two balanced orders with the same tie set orient
  every hinge edge outside the tie set alike (the hinge graph outside `T` is a forest,
  and a forest orientation is determined by its in-degrees);
* `card_fiber_pairsOrdered`: prescribing the order of `|P|` disjoint pairs outside `T`
  divides the count by `2^{|P|}`;
* `HingeCat.card_balanced_fiber_mul_le`: the balanced orders with tie set `T` number at
  most `k! (N - k)! / 2^{matchCount}`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.CountExp

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain CountCubic

/-! ## Tie sets and fibers -/

private theorem mem_tieSet {N k : ℕ} {π : Equiv.Perm (Fin N)} {o : Fin N} :
    o ∈ tieSet k π ↔ ((π o : Fin N) : ℕ) < k := by
  simp [tieSet]

theorem card_tieSet {N k : ℕ} (hk : k ≤ N) (π : Equiv.Perm (Fin N)) :
    (tieSet k π).card = k := by
  have h : (tieSet k π).map (π.toEmbedding.trans Fin.valEmbedding) = range k := by
    ext n
    simp only [mem_map, mem_tieSet, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ho
    · intro hn
      refine ⟨π.symm ⟨n, by omega⟩, ?_, ?_⟩ <;> simp [hn]
  have := congrArg Finset.card h
  rwa [card_map, card_range] at this

/-- Precomposition with a permutation `σ` moves fibers: if `σ` maps `T'` onto `T`,
then `π ↦ π * σ` maps the fiber of `T` into the fiber of `T'`. -/
private theorem tieSet_mul {N k : ℕ} (π σ : Equiv.Perm (Fin N)) :
    tieSet k (π * σ) = (tieSet k π).preimage σ (σ.injective.injOn _) := by
  ext o
  simp [mem_tieSet]

private theorem subtypeCongr_apply_pos {α : Type*} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
    {a : α} (h : p a) : Equiv.subtypeCongr e f a = e ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, h]

private theorem subtypeCongr_apply_neg {α : Type*} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
    {a : α} (h : ¬p a) : Equiv.subtypeCongr e f a = f ⟨a, h⟩ := by
  simp [Equiv.subtypeCongr, h]

private theorem card_fiber_eq {N k : ℕ} {T T' : Finset (Fin N)} (h : T.card = T'.card) :
    (fiber k T).card = (fiber k T').card := by
  classical
  have hc : Fintype.card {x // x ∈ T'} = Fintype.card {x // x ∈ T} := by simp [h]
  have hc' : Fintype.card {x // ¬ x ∈ T'} = Fintype.card {x // ¬ x ∈ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hc]
  let σ : Equiv.Perm (Fin N) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hc) (Fintype.equivOfCardEq hc')
  have hσ : ∀ x, x ∈ T' ↔ σ x ∈ T := by
    intro x
    by_cases hx : x ∈ T'
    · have e1 : σ x = _ :=
        subtypeCongr_apply_pos (p := fun y => y ∈ T') (q := fun y => y ∈ T) _ _ hx
      rw [e1]
      simp only [hx, true_iff]
      exact ((Fintype.equivOfCardEq hc) ⟨x, hx⟩).2
    · have e1 : σ x = _ :=
        subtypeCongr_apply_neg (p := fun y => y ∈ T') (q := fun y => y ∈ T) _ _ hx
      rw [e1]
      simp only [hx, false_iff]
      exact ((Fintype.equivOfCardEq hc') ⟨x, hx⟩).2
  refine card_congr (fun π _ => π * σ) ?_ ?_ ?_
  · intro π hπ
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    ext x
    simp [mem_tieSet, hσ x, ← hπ]
  · intro a b _ _ hab
    exact mul_right_cancel hab
  · intro π hπ
    refine ⟨π * σ⁻¹, ?_, by simp⟩
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    ext x
    have := hσ (σ⁻¹ x)
    simp only [Equiv.Perm.apply_inv_self] at this
    simp [mem_tieSet, ← this, ← hπ]

theorem card_fiber {N k : ℕ} {T : Finset (Fin N)} (hT : T.card = k) :
    (fiber k T).card = k ! * (N - k)! := by
  classical
  have hkN : k ≤ N := by
    have := card_le_univ T
    rw [Fintype.card_fin, hT] at this
    exact this
  have hsum : (univ : Finset (Equiv.Perm (Fin N))).card =
      ∑ T' in powersetCard k (univ : Finset (Fin N)), (fiber k T').card := by
    rw [card_eq_sum_card_fiberwise (f := tieSet k) (t := powersetCard k univ)]
    · rfl
    · intro π _
      simp [mem_powersetCard, card_tieSet hkN]
  have hall : ∀ T' ∈ powersetCard k (univ : Finset (Fin N)),
      (fiber k T').card = (fiber k T).card := by
    intro T' hT'
    rw [mem_powersetCard] at hT'
    exact card_fiber_eq (hT'.2.trans hT.symm)
  rw [sum_congr rfl hall, sum_const, card_powersetCard, card_univ, Fintype.card_perm,
    card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hpos : 0 < N.choose k := Nat.choose_pos hkN
  have := Nat.choose_mul_factorial_mul_factorial hkN
  rw [mul_assoc] at this
  exact (Nat.eq_of_mul_eq_mul_left hpos (this.trans hsum)).symm

/-! ## Orders with prescribed pairs -/

private theorem tieSet_mul_swap {N k : ℕ} {π : Equiv.Perm (Fin N)} {a b : Fin N}
    (ha : a ∉ tieSet k π) (hb : b ∉ tieSet k π) :
    tieSet k (π * Equiv.swap a b) = tieSet k π := by
  ext x
  rw [mem_tieSet, mem_tieSet, Equiv.Perm.mul_apply]
  rw [mem_tieSet] at ha hb
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left]
    exact iff_of_false hb ha
  by_cases hxb : x = b
  · subst hxb
    rw [Equiv.swap_apply_right]
    exact iff_of_false ha hb
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

open Classical in
theorem card_fiber_pairsOrdered {N k : ℕ} {T : Finset (Fin N)} (hT : T.card = k)
    (P : Finset (Fin N × Fin N)) (hne : ∀ p ∈ P, p.1 ≠ p.2)
    (hdisj : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2)
    (hout : ∀ p ∈ P, p.1 ∉ T ∧ p.2 ∉ T) :
    ((fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2).card * 2 ^ P.card =
      k ! * (N - k)! := by
  revert hne hdisj hout
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp only [not_mem_empty, IsEmpty.forall_iff, implies_true, filter_True, card_empty,
      pow_zero, mul_one]
    exact card_fiber hT
  | @insert p P hp ih =>
    intro hne hdisj hout
    have hne' : ∀ q ∈ P, q.1 ≠ q.2 := fun q hq => hne q (mem_insert_of_mem hq)
    have hdisj' : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' →
        q.1 ≠ q'.1 ∧ q.1 ≠ q'.2 ∧ q.2 ≠ q'.1 ∧ q.2 ≠ q'.2 :=
      fun q hq q' hq' => hdisj q (mem_insert_of_mem hq) q' (mem_insert_of_mem hq')
    have hout' : ∀ q ∈ P, q.1 ∉ T ∧ q.2 ∉ T := fun q hq => hout q (mem_insert_of_mem hq)
    have IH := ih hne' hdisj' hout'
    set S := (fiber k T).filter fun π => ∀ q ∈ P, π q.1 < π q.2 with hS
    have hS' : ((fiber k T).filter fun π => ∀ q ∈ insert p P, π q.1 < π q.2) =
        S.filter fun π => π p.1 < π p.2 := by
      ext π
      simp only [hS, mem_filter, forall_mem_insert]
      tauto
    have hp1 := (hout p (mem_insert_self p P)).1
    have hp2 := (hout p (mem_insert_self p P)).2
    have hpne := hne p (mem_insert_self p P)
    -- the involution `π ↦ π * swap p.1 p.2` preserves `S`
    have hmapS : ∀ π ∈ S, π * Equiv.swap p.1 p.2 ∈ S := by
      intro π hπ
      simp only [hS, fiber, mem_filter, mem_univ, true_and] at hπ ⊢
      refine ⟨?_, ?_⟩
      · rw [tieSet_mul_swap (hπ.1 ▸ hp1) (hπ.1 ▸ hp2), hπ.1]
      · intro q hq
        have hqp : p ≠ q := fun h => hp (h ▸ hq)
        obtain ⟨h1, h2, h3, h4⟩ := hdisj p (mem_insert_self p P) q (mem_insert_of_mem hq) hqp
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h3),
          Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) (Ne.symm h4)]
        exact hπ.2 q hq
    have hhalf : (S.filter fun π => π p.1 < π p.2).card =
        (S.filter fun π => ¬ π p.1 < π p.2).card := by
      refine card_congr (fun π _ => π * Equiv.swap p.1 p.2) ?_ ?_ ?_
      · intro π hπ
        rw [mem_filter] at hπ ⊢
        refine ⟨hmapS π hπ.1, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
        exact not_lt.mpr hπ.2.le
      · intro a b _ _ hab
        exact mul_right_cancel hab
      · intro π hπ
        rw [mem_filter] at hπ
        refine ⟨π * Equiv.swap p.1 p.2, ?_, ?_⟩
        · rw [mem_filter]
          refine ⟨hmapS π hπ.1, ?_⟩
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
            Equiv.swap_apply_right]
          have : π p.1 ≠ π p.2 := fun h => hpne (π.injective h)
          exact lt_of_le_of_ne (not_lt.mp hπ.2) (Ne.symm this)
        · show π * Equiv.swap p.1 p.2 * Equiv.swap p.1 p.2 = π
          rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := S) (fun π => π p.1 < π p.2)
    rw [← hhalf] at hsplit
    rw [hS', card_insert_of_not_mem hp, pow_succ, ← IH, ← hsplit]
    ring

/-! ## The hinge forest as a rooted forest -/

namespace HingeCat

variable {N : ℕ} (H : HingeCat N)

private theorem adj_symm {u v : Fin N} (h : H.Adj u v) : H.Adj v u := by
  unfold Adj at h ⊢
  rcases h with ⟨i, hi, h | h⟩ | h | h
  · exact Or.inl ⟨i, hi, Or.inr ⟨h.2, h.1⟩⟩
  · exact Or.inl ⟨i, hi, Or.inl ⟨h.2, h.1⟩⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private theorem lp_spine (hH : H.WF) {i : ℕ} (hi : i ≤ H.q) : H.lp (H.s i) = none := by
  cases h : H.lp (H.s i) with
  | none => rfl
  | some j =>
    exact absurd ⟨i, mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩ (hH.lp_not_spine _ j h)

private theorem lt_of_mem_links (hH : H.WF) {i : ℕ} (hi : i ∈ H.links) : i < H.q :=
  mem_range.mp (hH.links_sub hi)

/-- The parent of a vertex in the hinge forest rooted at the end `s q` of the spine:
a pendant vertex hangs off its spine vertex, and `s i` with `i ∈ links` has parent
`s (i + 1)`. -/
private noncomputable def par (v : Fin N) : Option (Fin N) :=
  match H.lp v with
  | some i => some (H.s i)
  | none =>
    if h : ∃ i, i ∈ H.links ∧ H.s i = v then some (H.s (Classical.choose h + 1)) else none

/-- The height of a vertex: `0` for a pendant vertex, `i + 1` for the spine vertex `s i`. -/
private noncomputable def ht (v : Fin N) : ℕ :=
  match H.lp v with
  | some _ => 0
  | none => if h : ∃ i, i ≤ H.q ∧ H.s i = v then Classical.choose h + 1 else 0

private theorem par_eq_some_iff (hH : H.WF) {v w : Fin N} :
    H.par v = some w ↔
      (∃ i, H.lp v = some i ∧ w = H.s i) ∨ (∃ i ∈ H.links, v = H.s i ∧ w = H.s (i + 1)) := by
  constructor
  · intro hp
    unfold par at hp
    cases hl : H.lp v with
    | some i =>
      rw [hl] at hp
      exact Or.inl ⟨i, rfl, (Option.some.inj hp).symm⟩
    | none =>
      rw [hl] at hp
      simp only at hp
      split_ifs at hp with h
      · have hs := Classical.choose_spec h
        exact Or.inr ⟨_, hs.1, hs.2.symm, (Option.some.inj hp).symm⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · unfold par
      rw [hi]
    · have hiq := H.lt_of_mem_links hH hi
      unfold par
      rw [H.lp_spine hH hiq.le]
      simp only
      have h : ∃ j, j ∈ H.links ∧ H.s j = H.s i := ⟨i, hi, rfl⟩
      rw [dif_pos h]
      have hs := Classical.choose_spec h
      have hjq := H.lt_of_mem_links hH hs.1
      rw [hH.s_inj _ hjq.le _ hiq.le hs.2]

private theorem ht_spine (hH : H.WF) {i : ℕ} (hi : i ≤ H.q) : H.ht (H.s i) = i + 1 := by
  unfold ht
  rw [H.lp_spine hH hi]
  simp only
  have h : ∃ j, j ≤ H.q ∧ H.s j = H.s i := ⟨i, hi, rfl⟩
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  rw [hH.s_inj _ hs.1 _ hi hs.2]

private theorem ht_lt (hH : H.WF) {v w : Fin N} (h : H.par v = some w) : H.ht v < H.ht w := by
  rcases (H.par_eq_some_iff hH).mp h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl, rfl⟩
  · have hv : H.ht v = 0 := by unfold ht; rw [hi]
    rw [hv, H.ht_spine hH (hH.lp_le _ _ hi)]
    exact Nat.succ_pos i
  · have hiq := H.lt_of_mem_links hH hi
    rw [H.ht_spine hH hiq.le, H.ht_spine hH hiq]
    exact Nat.lt_succ_self _

private theorem forestAdj_par_iff (hH : H.WF) {u v : Fin N} :
    ForestAdj H.par u v ↔ H.Adj u v := by
  unfold ForestAdj Adj
  rw [H.par_eq_some_iff hH, H.par_eq_some_iff hH]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl, rfl⟩) | (⟨i, hi, rfl⟩ | ⟨i, hi, rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
  · rintro (⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, hi, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)

/-- The hinge forest restricted to the vertices outside `T`. -/
private noncomputable def parOut (T : Finset (Fin N)) (v : Fin N) : Option (Fin N) := by
  classical
  exact if v ∉ T ∧ ∃ w, H.par v = some w ∧ w ∉ T then H.par v else none

private theorem parOut_eq_some_iff (T : Finset (Fin N)) {v w : Fin N} :
    H.parOut T v = some w ↔ H.par v = some w ∧ v ∉ T ∧ w ∉ T := by
  unfold parOut
  split_ifs with h
  · constructor
    · intro hp
      obtain ⟨w', hw', hw'T⟩ := h.2
      rw [hw'] at hp
      cases Option.some.inj hp
      exact ⟨hw', h.1, hw'T⟩
    · exact fun hp => hp.1
  · constructor
    · intro hp; cases hp
    · intro hp
      exact absurd ⟨hp.2.1, w, hp.1, hp.2.2⟩ h

private theorem forestAdj_parOut_iff (hH : H.WF) (T : Finset (Fin N)) {u v : Fin N} :
    ForestAdj (H.parOut T) u v ↔ H.Adj u v ∧ u ∉ T ∧ v ∉ T := by
  rw [← H.forestAdj_par_iff hH]
  unfold ForestAdj
  rw [H.parOut_eq_some_iff, H.parOut_eq_some_iff]
  tauto

open Classical in
/-- Splitting the count of neighbours above `w ∉ T` into the neighbours in `T` and
the forest neighbours outside `T`. -/
private theorem upCount_split (hH : H.WF) {k : ℕ} {π : Equiv.Perm (Fin N)} {w : Fin N}
    (hw : w ∉ tieSet k π) :
    CountExp.upCount H.Adj π w =
      (univ.filter fun x => H.Adj w x ∧ x ∈ tieSet k π).card +
        CountCubic.upCount (H.parOut (tieSet k π)) (fun v => OrderDual.toDual (π v)) w := by
  classical
  unfold CountExp.upCount CountCubic.upCount
  rw [← card_disjoint_union]
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_union, H.forestAdj_parOut_iff hH,
      OrderDual.toDual_lt_toDual]
    have hw' := hw
    rw [mem_tieSet] at hw'
    by_cases hx : x ∈ tieSet k π
    · have := mem_tieSet.mp hx
      have hlt : π x < π w := by
        rw [Fin.lt_iff_val_lt_val]; exact lt_of_lt_of_le this (not_lt.mp hw')
      tauto
    · tauto
  · rw [disjoint_filter]
    intro x _ h1 h2
    exact ((H.forestAdj_parOut_iff hH _).mp h2.1).2.2 h1.2

end HingeCat

theorem HingeCat.orient_eq_of_balanced {N : ℕ} (H : HingeCat N) (hH : H.WF) {k : ℕ}
    {c : Fin N → ℝ} {π₁ π₂ : Equiv.Perm (Fin N)} (hT : tieSet k π₁ = tieSet k π₂)
    (h₁ : Balanced H.Adj c k π₁) (h₂ : Balanced H.Adj c k π₂) {u v : Fin N}
    (hu : u ∉ tieSet k π₁) (hv : v ∉ tieSet k π₁) (huv : H.Adj u v) :
    π₁ u < π₁ v ↔ π₂ u < π₂ v := by
  classical
  set T := tieSet k π₁ with hTdef
  let r₁ : Fin N → (Fin N)ᵒᵈ := fun v => OrderDual.toDual (π₁ v)
  let r₂ : Fin N → (Fin N)ᵒᵈ := fun v => OrderDual.toDual (π₂ v)
  have hμ : ∀ v p, H.parOut T v = some p → H.ht v < H.ht p :=
    fun v p h => H.ht_lt hH ((H.parOut_eq_some_iff T).mp h).1
  have hne : ∀ (π : Equiv.Perm (Fin N)) v p, H.parOut T v = some p →
      OrderDual.toDual (π v) ≠ OrderDual.toDual (π p) := by
    intro π v p h he
    have := hμ v p h
    rw [π.injective (OrderDual.toDual.injective he)] at this
    exact lt_irrefl _ this
  have hcount : ∀ w, CountCubic.upCount (H.parOut T) r₁ w =
      CountCubic.upCount (H.parOut T) r₂ w := by
    intro w
    by_cases hw : w ∈ T
    · have hz : ∀ r : Fin N → (Fin N)ᵒᵈ, CountCubic.upCount (H.parOut T) r w = 0 := by
        intro r
        unfold CountCubic.upCount
        rw [card_eq_zero, filter_eq_empty_iff]
        intro x _ hx
        exact ((H.forestAdj_parOut_iff hH T).mp hx.1).2.1 hw
      rw [hz, hz]
    · have hw₂ : w ∉ tieSet k π₂ := hT ▸ hw
      have e₁ := h₁ w (by rw [hTdef, mem_tieSet] at hw; exact not_lt.mp hw)
      have e₂ := h₂ w (by rw [mem_tieSet] at hw₂; exact not_lt.mp hw₂)
      have he : CountExp.upCount H.Adj π₁ w = CountExp.upCount H.Adj π₂ w := by
        exact_mod_cast e₁.trans e₂.symm
      rw [H.upCount_split hH hw, H.upCount_split hH hw₂, ← hT] at he
      exact Nat.add_left_cancel he
  have key := orient_eq_of_upCount_eq_all (H.parOut T) H.ht hμ r₁ r₂ (hne π₁) (hne π₂) hcount
  have hadj : ForestAdj (H.parOut T) u v := (H.forestAdj_parOut_iff hH T).mpr ⟨huv, hu, hv⟩
  rcases hadj with h | h
  · have huv' : u ≠ v := by
      intro e; have := hμ u v h; rw [e] at this; exact lt_irrefl _ this
    have k' := key u v h
    simp only [r₁, r₂, OrderDual.toDual_lt_toDual] at k'
    have n₁ : π₁ u ≠ π₁ v := fun e => huv' (π₁.injective e)
    have n₂ : π₂ u ≠ π₂ v := fun e => huv' (π₂.injective e)
    constructor
    · intro h1
      rcases lt_or_gt_of_ne n₂ with h2 | h2
      · exact h2
      · exact absurd (k'.mpr h2) (not_lt.mpr h1.le)
    · intro h2
      rcases lt_or_gt_of_ne n₁ with h1 | h1
      · exact h1
      · exact absurd (k'.mp h1) (not_lt.mpr h2.le)
  · have k' := key v u h
    simpa only [r₁, r₂, OrderDual.toDual_lt_toDual] using k'

/-! ## The greedy matching -/

private theorem chosen_spec {links A : Finset ℕ} {i : ℕ} (h : chosen links A i = true) :
    i ∈ links ∧ i ∉ A ∧ i + 1 ∉ A := by
  cases i with
  | zero => simpa [chosen] using h
  | succ i =>
    simp only [chosen, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

private theorem chosen_succ {links A : Finset ℕ} {i : ℕ} (h : chosen links A i = true) :
    chosen links A (i + 1) = false := by
  simp [chosen, h]

/-- Two pairs with four distinct ends. -/
private def PairDisj {N : ℕ} (e e' : Fin N × Fin N) : Prop :=
  e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2

private theorem PairDisj.symm {N : ℕ} {e e' : Fin N × Fin N} (h : PairDisj e e') : PairDisj e' e :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

private theorem PairDisj.swap_left {N : ℕ} {e e' : Fin N × Fin N} (h : PairDisj e e') :
    PairDisj e.swap e' :=
  ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩

private theorem PairDisj.swap_right {N : ℕ} {e e' : Fin N × Fin N} (h : PairDisj e e') :
    PairDisj e e'.swap :=
  (h.symm.swap_left).symm

/-- Orient a pair increasingly in the order of `π`. -/
private def orientBy {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Fin N × Fin N) : Fin N × Fin N :=
  if π e.1 < π e.2 then e else e.swap

private theorem orientBy_cases {N : ℕ} (π : Equiv.Perm (Fin N)) (e : Fin N × Fin N) :
    orientBy π e = e ∨ orientBy π e = e.swap := by
  unfold orientBy
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem orientBy_lt {N : ℕ} (π : Equiv.Perm (Fin N)) {e : Fin N × Fin N} (h : e.1 ≠ e.2) :
    π (orientBy π e).1 < π (orientBy π e).2 := by
  unfold orientBy
  split_ifs with h'
  · exact h'
  · have : π e.1 ≠ π e.2 := fun he => h (π.injective he)
    exact lt_of_le_of_ne (not_lt.mp h') (Ne.symm this)

private theorem PairDisj.orientBy {N : ℕ} (π π' : Equiv.Perm (Fin N)) {e e' : Fin N × Fin N}
    (h : PairDisj e e') : PairDisj (orientBy π e) (orientBy π' e') := by
  rcases orientBy_cases π e with h1 | h1 <;> rcases orientBy_cases π' e' with h2 | h2 <;>
    rw [h1, h2]
  · exact h
  · exact h.swap_right
  · exact h.swap_left
  · exact h.swap_left.swap_right

namespace HingeCat

variable {N : ℕ} (H : HingeCat N)

/-- A pendant vertex at the spine index `i` (when there is one). -/
private noncomputable def pend (i : ℕ) : Fin N := by
  classical
  exact if h : ∃ u, H.lp u = some i then Classical.choose h else H.s i

private theorem lp_pend {i : ℕ} (hi : i ∈ H.leafy) : H.lp (H.pend i) = some i := by
  have h : ∃ u, H.lp u = some i := (mem_filter.mp hi).2
  unfold pend
  rw [dif_pos h]
  exact Classical.choose_spec h

private theorem spine_ne_pendant (hH : H.WF) {i j : ℕ} (hi : i ≤ H.q) {u : Fin N}
    (hu : H.lp u = some j) : H.s i ≠ u := by
  rintro rfl
  exact hH.lp_not_spine _ j hu ⟨i, mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩

private theorem s_ne (hH : H.WF) {i j : ℕ} (hi : i ≤ H.q) (hj : j ≤ H.q) (hij : i ≠ j) :
    H.s i ≠ H.s j :=
  fun h => hij (hH.s_inj i hi j hj h)

/-- The edges of the matching: `inl i` is the spine edge `s i, s (i + 1)` and `inr i`
the pendant edge `s i, pend i`. -/
private noncomputable def mEdge : ℕ ⊕ ℕ → Fin N × Fin N
  | Sum.inl i => (H.s i, H.s (i + 1))
  | Sum.inr i => (H.s i, H.pend i)

end HingeCat

open Classical in
theorem HingeCat.card_balanced_fiber_mul_le {N : ℕ} (H : HingeCat N) (hH : H.WF) {k : ℕ}
    (hk : k ≤ N) (T : Finset (Fin N)) (hT : ∀ u i, H.lp u = some i → (u ∈ T ↔ H.s i ∈ T))
    (c : Fin N → ℝ) :
    ((fiber k T).filter (Balanced H.Adj c k)).card *
        2 ^ matchCount H.q H.links H.leafy (H.spineIdx T) ≤ k ! * (N - k)! := by
  by_cases hex : ∃ π₀, π₀ ∈ (fiber k T).filter (Balanced H.Adj c k)
  swap
  · rw [not_exists] at hex
    rw [card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr hex), zero_mul]
    exact Nat.zero_le _
  obtain ⟨π₀, hπ₀⟩ := hex
  simp only [fiber, mem_filter, mem_univ, true_and] at hπ₀
  obtain ⟨hπ₀T, hπ₀b⟩ := hπ₀
  have hTk : T.card = k := hπ₀T ▸ card_tieSet hk π₀
  set A := H.spineIdx T
  set C := (range H.q).filter fun i => chosen H.links A i = true with hC
  set D := (range (H.q + 1)).filter fun i => Single H.links i ∧ i ∈ H.leafy ∧ i ∉ A with hD
  set E := C.disjSum D with hE
  have hmc : matchCount H.q H.links H.leafy A = E.card := by
    rw [hE, card_disjSum]
    rfl
  have notA : ∀ i, i ≤ H.q → i ∉ A → H.s i ∉ T := by
    intro i hi hiA hiT
    exact hiA (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hi), hiT⟩)
  -- facts on the edges
  have memC : ∀ i, i ∈ C → i < H.q ∧ chosen H.links A i = true := by
    intro i hi
    rw [hC, mem_filter, mem_range] at hi
    exact hi
  have memD : ∀ j, j ∈ D → j ≤ H.q ∧ Single H.links j ∧ j ∈ H.leafy ∧ j ∉ A := by
    intro j hj
    rw [hD, mem_filter, mem_range] at hj
    exact ⟨Nat.le_of_lt_succ hj.1, hj.2⟩
  have F1 : ∀ α ∈ E, H.Adj (H.mEdge α).1 (H.mEdge α).2 := by
    rintro (i | j) hα
    · have hi := memC i (by simpa [hE] using hα)
      exact Or.inl ⟨i, (chosen_spec hi.2).1, Or.inl ⟨rfl, rfl⟩⟩
    · have hj := memD j (by simpa [hE] using hα)
      exact Or.inr (Or.inr ⟨j, H.lp_pend hj.2.2.1, rfl⟩)
  have F2 : ∀ α ∈ E, (H.mEdge α).1 ∉ T ∧ (H.mEdge α).2 ∉ T := by
    rintro (i | j) hα
    · have hi := memC i (by simpa [hE] using hα)
      have hs := chosen_spec hi.2
      exact ⟨notA i hi.1.le hs.2.1, notA (i + 1) hi.1 hs.2.2⟩
    · have hj := memD j (by simpa [hE] using hα)
      have h1 := notA j hj.1 hj.2.2.2
      refine ⟨h1, ?_⟩
      show H.pend j ∉ T
      rw [hT _ j (H.lp_pend hj.2.2.1)]
      exact h1
  have F4 : ∀ α ∈ E, (H.mEdge α).1 ≠ (H.mEdge α).2 := by
    rintro (i | j) hα
    · have hi := memC i (by simpa [hE] using hα)
      exact H.s_ne hH hi.1.le hi.1 (Nat.ne_of_lt (Nat.lt_succ_self i))
    · have hj := memD j (by simpa [hE] using hα)
      exact H.spine_ne_pendant hH hj.1 (H.lp_pend hj.2.2.1)
  have SP : ∀ i ∈ C, ∀ j ∈ D, PairDisj (H.mEdge (Sum.inl i)) (H.mEdge (Sum.inr j)) := by
    intro i hi j hj
    obtain ⟨hiq, hic⟩ := memC i hi
    obtain ⟨hjq, hjs, hjl, -⟩ := memD j hj
    have hil := (chosen_spec hic).1
    have hlp := H.lp_pend hjl
    have hij : i ≠ j := fun e => hjs.2 (e ▸ hil)
    have hij' : i + 1 ≠ j := by
      intro e
      rcases hjs.1 with h0 | h0
      · exact Nat.succ_ne_zero i (e.trans h0)
      · rw [← e, Nat.add_sub_cancel] at h0
        exact h0 hil
    exact ⟨H.s_ne hH hiq.le hjq hij, H.spine_ne_pendant hH hiq.le hlp,
      H.s_ne hH hiq hjq hij', H.spine_ne_pendant hH hiq hlp⟩
  have F3 : ∀ α ∈ E, ∀ β ∈ E, α ≠ β → PairDisj (H.mEdge α) (H.mEdge β) := by
    rintro (i | i) hα (j | j) hβ hne
    · have hi := memC i (by simpa [hE] using hα)
      have hj := memC j (by simpa [hE] using hβ)
      have hij : i ≠ j := fun e => hne (e ▸ rfl)
      have h1 : i ≠ j + 1 := by
        intro e
        have := chosen_succ hj.2
        rw [← e, hi.2] at this
        exact Bool.noConfusion this
      have h2 : i + 1 ≠ j := by
        intro e
        have := chosen_succ hi.2
        rw [e, hj.2] at this
        exact Bool.noConfusion this
      have h3 : i + 1 ≠ j + 1 := fun e => hij (Nat.succ.inj e)
      exact ⟨H.s_ne hH hi.1.le hj.1.le hij, H.s_ne hH hi.1.le hj.1 h1,
        H.s_ne hH hi.1 hj.1.le h2, H.s_ne hH hi.1 hj.1 h3⟩
    · exact SP i (by simpa [hE] using hα) j (by simpa [hE] using hβ)
    · exact (SP j (by simpa [hE] using hβ) i (by simpa [hE] using hα)).symm
    · have hi := memD i (by simpa [hE] using hα)
      have hj := memD j (by simpa [hE] using hβ)
      have hij : i ≠ j := fun e => hne (e ▸ rfl)
      have hli := H.lp_pend hi.2.2.1
      have hlj := H.lp_pend hj.2.2.1
      refine ⟨H.s_ne hH hi.1 hj.1 hij, H.spine_ne_pendant hH hi.1 hlj,
        (H.spine_ne_pendant hH hj.1 hli).symm, ?_⟩
      intro e
      change H.pend i = H.pend j at e
      rw [e, hlj] at hli
      exact hij (Option.some.inj hli).symm
  -- the oriented pairs
  set P := E.image fun α => orientBy π₀ (H.mEdge α) with hP
  have hPcard : P.card = E.card := by
    rw [hP]
    refine card_image_of_injOn ?_
    intro α hα β hβ he
    by_contra hne
    exact ((F3 α hα β hβ hne).orientBy π₀ π₀).1 (congrArg Prod.fst he)
  have memP : ∀ p ∈ P, ∃ α ∈ E, p = orientBy π₀ (H.mEdge α) := by
    intro p hp
    obtain ⟨α, hα, rfl⟩ := mem_image.mp hp
    exact ⟨α, hα, rfl⟩
  have orient_adj : ∀ α ∈ E, H.Adj (orientBy π₀ (H.mEdge α)).1 (orientBy π₀ (H.mEdge α)).2 ∧
      (orientBy π₀ (H.mEdge α)).1 ∉ T ∧ (orientBy π₀ (H.mEdge α)).2 ∉ T ∧
      (orientBy π₀ (H.mEdge α)).1 ≠ (orientBy π₀ (H.mEdge α)).2 := by
    intro α hα
    rcases orientBy_cases π₀ (H.mEdge α) with h | h <;> rw [h]
    · exact ⟨F1 α hα, (F2 α hα).1, (F2 α hα).2, F4 α hα⟩
    · exact ⟨H.adj_symm (F1 α hα), (F2 α hα).2, (F2 α hα).1, (F4 α hα).symm⟩
  have hne : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨α, hα, rfl⟩ := memP p hp
    exact (orient_adj α hα).2.2.2
  have hdisj : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2 := by
    intro p hp p' hp' hpp
    obtain ⟨α, hα, rfl⟩ := memP p hp
    obtain ⟨β, hβ, rfl⟩ := memP p' hp'
    have hab : α ≠ β := by rintro rfl; exact hpp rfl
    exact (F3 α hα β hβ hab).orientBy π₀ π₀
  have hout : ∀ p ∈ P, p.1 ∉ T ∧ p.2 ∉ T := by
    intro p hp
    obtain ⟨α, hα, rfl⟩ := memP p hp
    exact ⟨(orient_adj α hα).2.1, (orient_adj α hα).2.2.1⟩
  have hsub : (fiber k T).filter (Balanced H.Adj c k) ⊆
      (fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2 := by
    intro π hπ
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    refine ⟨hπ.1, ?_⟩
    intro p hp
    obtain ⟨α, hα, rfl⟩ := memP p hp
    obtain ⟨hadj, h1, h2, -⟩ := orient_adj α hα
    have key := H.orient_eq_of_balanced hH (hπ₀T.trans hπ.1.symm) hπ₀b hπ.2
      (hπ₀T.symm ▸ h1) (hπ₀T.symm ▸ h2) hadj
    exact key.mp (orientBy_lt π₀ (F4 α hα))
  have hcount := card_fiber_pairsOrdered hTk P hne hdisj hout
  rw [hmc, ← hPcard, ← hcount]
  exact Nat.mul_le_mul_right _ (card_le_of_subset hsub)

end MaxCaterpillar.CountExp
