import MaxNN.Constructions.Paramid.Geom.Kuhn.Hull

/-!
# Cutting a polytope into the chambers of a braid arrangement

Helper for `Geom/Kuhn.lean` (namespace `MaxNN.ParamidGeom.Kuhn`).

Let `α : Fin k → ℝ^m` be injective, so that every hyperplane `⟨α i − α j, ·⟩ = 0` (`i ≠ j`) has a
nonzero normal.  For a list `l` of indices, `chamber α l` is the closed set on which the
functionals `⟨α i, ·⟩` weakly decrease along `l`.

* `staircase`: inserting a new index `t` into a chamber list `ys` is a staircase of cuts.  Cut by
  `⟨α t, ·⟩ = ⟨α y, ·⟩` for the head `y` of `ys`: the upper half is the chamber of `t :: ys`, the
  lower half is cut further.  The leaves are exactly the insertions `List.permutations'Aux t ys`,
  and every cut costs only an element of `LSpan m (m − 1)` (`hS_cut_mem_LSpan`).
* `chamber_decomp`: inserting all indices of a duplicate-free list `ts` gives the leaves
  `List.permutations' ts`.
* `exists_chamber_pieces`: for `ts = finRange k` the leaves are reindexed by
  `Equiv.Perm (Fin k)`: modulo `LSpan m (m − 1)`, `hS S` is the sum over `σ` of the support
  functions of finite sets `P σ` with `conv (P σ) = conv S ∩ {⟨α (σ 0), ·⟩ ≥ ⟨α (σ 1), ·⟩ ≥ …}`.
-/

namespace MaxNN.ParamidGeom.Kuhn

open BigOperators MaxNN.SupportCut

variable {m k : ℕ}

/-- The chamber of the list `l`: the points where `⟨α i, ·⟩` weakly decreases along `l`. -/
def chamber (α : Fin k → Fin m → ℝ) (l : List (Fin k)) : Set (Fin m → ℝ) :=
  {x | l.Pairwise (fun i j => dot (α j) x ≤ dot (α i) x)}

theorem mem_chamber {α : Fin k → Fin m → ℝ} {l : List (Fin k)} {x : Fin m → ℝ} :
    x ∈ chamber α l ↔ l.Pairwise (fun i j => dot (α j) x ≤ dot (α i) x) := Iff.rfl

/-! ## Insertions of one element -/

theorem perm_of_mem_permutations'Aux {β : Type*} (t : β) :
    ∀ {ys l : List β}, l ∈ List.permutations'Aux t ys → l.Perm (t :: ys)
  | [], l, h => by
      simp only [List.permutations'Aux, List.mem_singleton] at h
      rw [h]
  | y :: ys, l, h => by
      simp only [List.permutations'Aux, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨l', hl', rfl⟩
      · rw [h]
      · exact ((perm_of_mem_permutations'Aux t hl').cons y).trans (List.Perm.swap t y ys)

theorem sublist_of_mem_permutations'Aux {β : Type*} (t : β) :
    ∀ {ys l : List β}, l ∈ List.permutations'Aux t ys → ys.Sublist l
  | [], _, _ => List.nil_sublist _
  | y :: ys, l, h => by
      simp only [List.permutations'Aux, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨l', hl', rfl⟩
      · rw [h]
        exact List.sublist_cons t (y :: ys)
      · exact (sublist_of_mem_permutations'Aux t hl').cons₂ y

theorem erase_of_mem_permutations'Aux {β : Type*} [DecidableEq β] (t : β) :
    ∀ {ys l : List β}, t ∉ ys → l ∈ List.permutations'Aux t ys → l.erase t = ys
  | [], l, _, h => by
      simp only [List.permutations'Aux, List.mem_singleton] at h
      rw [h, List.erase_cons_head]
  | y :: ys, l, ht, h => by
      have hyt : y ≠ t := fun e => ht (by rw [← e]; exact List.mem_cons_self y ys)
      have hys : t ∉ ys := fun e => ht (List.mem_cons_of_mem y e)
      simp only [List.permutations'Aux, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨l', hl', rfl⟩
      · rw [h, List.erase_cons_head]
      · rw [List.erase_cons_tail l' hyt, erase_of_mem_permutations'Aux t hys hl']

/-! ## The staircase of cuts inserting one index -/

/-- **Staircase.**  If `conv S` lies in the chamber of `ys` and `t ∉ ys`, then modulo
`LSpan m (m − 1)`, `hS S` is the sum of `hS (P l)` over the insertions `l` of `t` into `ys`, with
`conv (P l) = conv S ∩ chamber α l`. -/
theorem staircase (α : Fin k → Fin m → ℝ) (hα : Function.Injective α) (t : Fin k) :
    ∀ (ys : List (Fin k)), t ∉ ys → ∀ (S : Finset (Fin m → ℝ)),
      convexHull ℝ (S : Set (Fin m → ℝ)) ⊆ chamber α ys →
      ∃ P : List (Fin k) → Finset (Fin m → ℝ),
        (∀ l ∈ List.permutations'Aux t ys,
          convexHull ℝ (P l : Set (Fin m → ℝ)) =
            convexHull ℝ (S : Set (Fin m → ℝ)) ∩ chamber α l) ∧
        hS S - ((List.permutations'Aux t ys).map (fun l => hS (P l))).sum ∈ LSpan m (m - 1)
  | [], _, S, _ => by
      refine ⟨fun _ => S, ?_, ?_⟩
      · intro l hl
        simp only [List.permutations'Aux, List.mem_singleton] at hl
        subst hl
        ext x
        simp only [Set.mem_inter_iff, mem_chamber, List.pairwise_singleton, and_true]
      · simp only [List.permutations'Aux, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, sub_self]
        exact Submodule.zero_mem _
  | y :: ys, ht, S, hSc => by
      have hty : t ≠ y := fun e => ht (by rw [e]; exact List.mem_cons_self y ys)
      have hys : t ∉ ys := fun e => ht (List.mem_cons_of_mem y e)
      have ha : α t - α y ≠ 0 := sub_ne_zero.mpr (fun h => hty (hα h))
      have hdot : ∀ x, dot (α t - α y) x = dot (α t) x - dot (α y) x :=
        fun x => dot_sub_left _ _ _
      have hU : convexHull ℝ (upperPoints S (α t - α y) 0 : Set (Fin m → ℝ)) =
          convexHull ℝ (S : Set (Fin m → ℝ)) ∩ {x | 0 ≤ dot (α t - α y) x} :=
        (convexHull_inter_halfspace_ge S (α t - α y) 0).symm
      have hL : convexHull ℝ (lowerPoints S (α t - α y) 0 : Set (Fin m → ℝ)) =
          convexHull ℝ (S : Set (Fin m → ℝ)) ∩ {x | dot (α t - α y) x ≤ 0} :=
        (convexHull_inter_halfspace_le S (α t - α y) 0).symm
      have hLsub : convexHull ℝ (lowerPoints S (α t - α y) 0 : Set (Fin m → ℝ)) ⊆
          chamber α ys := by
        rw [hL]
        intro x hx
        exact (List.pairwise_cons.mp (hSc hx.1)).2
      obtain ⟨P₀, hP₀, hsum₀⟩ := staircase α hα t ys hys (lowerPoints S (α t - α y) 0) hLsub
      have hne : ∀ l' : List (Fin k), (y :: l') ≠ t :: y :: ys := fun l' h =>
        hty (List.cons.inj h).1.symm
      refine ⟨fun l => if l = t :: y :: ys then upperPoints S (α t - α y) 0 else P₀ l.tail,
        ?_, ?_⟩
      · intro l hl
        simp only [List.permutations'Aux, List.mem_cons, List.mem_map] at hl
        rcases hl with rfl | ⟨l', hl', rfl⟩
        · dsimp only
          rw [if_pos rfl, hU]
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_chamber]
          constructor
          · rintro ⟨hx, hax⟩
            refine ⟨hx, ?_⟩
            have hc := List.pairwise_cons.mp (hSc hx)
            rw [hdot] at hax
            refine List.pairwise_cons.mpr ⟨?_, hSc hx⟩
            intro z hz
            rcases List.mem_cons.mp hz with hz | hz
            · rw [hz]
              linarith
            · linarith [hc.1 z hz]
          · rintro ⟨hx, hc⟩
            refine ⟨hx, ?_⟩
            have h1 := (List.pairwise_cons.mp hc).1 y (List.mem_cons_self y ys)
            rw [hdot]
            linarith
        · dsimp only
          rw [if_neg (hne l'), List.tail_cons, hP₀ l' hl', hL]
          have hperm := perm_of_mem_permutations'Aux t hl'
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_chamber]
          constructor
          · rintro ⟨⟨hx, hax⟩, hl'x⟩
            refine ⟨hx, List.pairwise_cons.mpr ⟨?_, hl'x⟩⟩
            intro z hz
            rw [hdot] at hax
            rcases List.mem_cons.mp (hperm.subset hz) with hz' | hz'
            · rw [hz']
              linarith
            · exact (List.pairwise_cons.mp (hSc hx)).1 z hz'
          · rintro ⟨hx, hc⟩
            obtain ⟨hc1, hc2⟩ := List.pairwise_cons.mp hc
            have htl : t ∈ l' := hperm.symm.subset (List.mem_cons_self t ys)
            have h1 := hc1 t htl
            refine ⟨⟨hx, ?_⟩, hc2⟩
            rw [hdot]
            linarith
      · have hmap : (List.permutations'Aux t (y :: ys)).map
            (fun l => hS (if l = t :: y :: ys then upperPoints S (α t - α y) 0
              else P₀ l.tail)) =
            hS (upperPoints S (α t - α y) 0) ::
              (List.permutations'Aux t ys).map (fun l' => hS (P₀ l')) := by
          simp only [List.permutations'Aux, List.map_cons, List.map_map, ite_true]
          congr 1
          apply List.map_congr
          intro l' _
          simp only [Function.comp_apply, if_neg (hne l'), List.tail_cons]
        rw [hmap, List.sum_cons]
        have e : hS S - (hS (upperPoints S (α t - α y) 0) +
            ((List.permutations'Aux t ys).map (fun l' => hS (P₀ l'))).sum) =
            (hS S - (hS (upperPoints S (α t - α y) 0) + hS (lowerPoints S (α t - α y) 0))) +
            (hS (lowerPoints S (α t - α y) 0) -
              ((List.permutations'Aux t ys).map (fun l' => hS (P₀ l'))).sum) := by abel
        rw [e]
        exact add_mem (hS_cut_mem_LSpan S ha 0) hsum₀

/-! ## Inserting all indices -/

theorem sum_map_bind {β γ M : Type*} [AddCommMonoid M] (L : List β) (f : β → List γ)
    (g : γ → M) :
    ((L.bind f).map g).sum = (L.map (fun a => ((f a).map g).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.cons_bind, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

/-- **Chamber decomposition along a list.**  Modulo `LSpan m (m − 1)`, `hS S` is the sum of
`hS (P l)` over the permutations `l` of `ts`, with `conv (P l) = conv S ∩ chamber α l`. -/
theorem chamber_decomp (α : Fin k → Fin m → ℝ) (hα : Function.Injective α) :
    ∀ (ts : List (Fin k)), ts.Nodup → ∀ (S : Finset (Fin m → ℝ)),
      ∃ P : List (Fin k) → Finset (Fin m → ℝ),
        (∀ l ∈ List.permutations' ts,
          convexHull ℝ (P l : Set (Fin m → ℝ)) =
            convexHull ℝ (S : Set (Fin m → ℝ)) ∩ chamber α l) ∧
        hS S - ((List.permutations' ts).map (fun l => hS (P l))).sum ∈ LSpan m (m - 1)
  | [], _, S => by
      refine ⟨fun _ => S, ?_, ?_⟩
      · intro l hl
        simp only [List.permutations', List.mem_singleton] at hl
        subst hl
        ext x
        exact ⟨fun h => ⟨h, List.Pairwise.nil⟩, fun h => h.1⟩
      · simp only [List.permutations', List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, sub_self]
        exact Submodule.zero_mem _
  | t :: ts, hnd, S => by
      have ht : t ∉ ts := (List.nodup_cons.mp hnd).1
      have hnd' : ts.Nodup := (List.nodup_cons.mp hnd).2
      obtain ⟨P₀, hP₀, hsum₀⟩ := chamber_decomp α hα ts hnd' S
      have htl : ∀ l₀ ∈ List.permutations' ts, t ∉ l₀ := fun l₀ hl₀ h =>
        ht ((List.mem_permutations'.mp hl₀).subset h)
      have hstep : ∀ l₀ : List (Fin k), ∃ Q : List (Fin k) → Finset (Fin m → ℝ),
          l₀ ∈ List.permutations' ts →
            (∀ l ∈ List.permutations'Aux t l₀,
              convexHull ℝ (Q l : Set (Fin m → ℝ)) =
                convexHull ℝ (P₀ l₀ : Set (Fin m → ℝ)) ∩ chamber α l) ∧
            hS (P₀ l₀) - ((List.permutations'Aux t l₀).map (fun l => hS (Q l))).sum ∈
              LSpan m (m - 1) := by
        intro l₀
        by_cases hl₀ : l₀ ∈ List.permutations' ts
        · have hsub : convexHull ℝ (P₀ l₀ : Set (Fin m → ℝ)) ⊆ chamber α l₀ := by
            rw [hP₀ l₀ hl₀]
            exact Set.inter_subset_right _ _
          obtain ⟨Q, hQ1, hQ2⟩ := staircase α hα t l₀ (htl l₀ hl₀) (P₀ l₀) hsub
          exact ⟨Q, fun _ => ⟨hQ1, hQ2⟩⟩
        · exact ⟨fun _ => ∅, fun h => absurd h hl₀⟩
      choose Q hQ using hstep
      refine ⟨fun l => Q (l.erase t) l, ?_, ?_⟩
      · intro l hl
        rw [List.permutations', List.mem_bind] at hl
        obtain ⟨l₀, hl₀, hl⟩ := hl
        have he : l.erase t = l₀ := erase_of_mem_permutations'Aux t (htl l₀ hl₀) hl
        have hsl : chamber α l ⊆ chamber α l₀ := fun x hx =>
          List.Pairwise.sublist (sublist_of_mem_permutations'Aux t hl) hx
        show convexHull ℝ (Q (l.erase t) l : Set (Fin m → ℝ)) = _
        rw [he, (hQ l₀ hl₀).1 l hl, hP₀ l₀ hl₀, Set.inter_assoc,
          Set.inter_eq_self_of_subset_right hsl]
      · rw [List.permutations', sum_map_bind]
        have hin : (List.permutations' ts).map
            (fun l₀ => ((List.permutations'Aux t l₀).map (fun l => hS (Q (l.erase t) l))).sum) =
            (List.permutations' ts).map
              (fun l₀ => ((List.permutations'Aux t l₀).map (fun l => hS (Q l₀ l))).sum) := by
          apply List.map_congr
          intro l₀ hl₀
          congr 1
          apply List.map_congr
          intro l hl
          rw [erase_of_mem_permutations'Aux t (htl l₀ hl₀) hl]
        rw [hin]
        have hdiff := list_sum_sub_mem_LSpan (List.permutations' ts) (fun l₀ => hS (P₀ l₀))
          (fun l₀ => ((List.permutations'Aux t l₀).map (fun l => hS (Q l₀ l))).sum)
          (fun l₀ hl₀ => (hQ l₀ hl₀).2)
        have e : hS S - ((List.permutations' ts).map
              (fun l₀ => ((List.permutations'Aux t l₀).map (fun l => hS (Q l₀ l))).sum)).sum =
            (hS S - ((List.permutations' ts).map (fun l₀ => hS (P₀ l₀))).sum) +
            (((List.permutations' ts).map (fun l₀ => hS (P₀ l₀))).sum -
              ((List.permutations' ts).map
                (fun l₀ => ((List.permutations'Aux t l₀).map
                  (fun l => hS (Q l₀ l))).sum)).sum) := by
          abel
        rw [e]
        exact add_mem hsum₀ hdiff

/-! ## Reindexing the permutations of `finRange k` by `Equiv.Perm (Fin k)` -/

theorem ofFn_perm_finRange (σ : Equiv.Perm (Fin k)) : (List.ofFn σ).Perm (List.finRange k) :=
  (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr σ.injective) (List.nodup_finRange k)).mpr
    fun a => ⟨fun _ => List.mem_finRange a,
      fun _ => (List.mem_ofFn σ a).mpr ⟨σ.symm a, σ.apply_symm_apply a⟩⟩

theorem exists_perm_ofFn_eq {l : List (Fin k)} (h : l.Perm (List.finRange k)) :
    ∃ σ : Equiv.Perm (Fin k), List.ofFn σ = l := by
  have hlen : l.length = k := by rw [h.length_eq, List.length_finRange]
  have hnd : l.Nodup := h.nodup_iff.mpr (List.nodup_finRange k)
  let f : Fin k → Fin k := fun p => l.get (Fin.cast hlen.symm p)
  have hf : Function.Injective f := by
    intro p q hpq
    have h1 := List.nodup_iff_injective_get.mp hnd hpq
    apply Fin.ext
    have h2 := congrArg Fin.val h1
    simpa using h2
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  show List.ofFn f = l
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.ofFn_congr hlen]

theorem sum_permutations'_finRange {M : Type*} [AddCommMonoid M] (F : List (Fin k) → M) :
    ((List.permutations' (List.finRange k)).map F).sum =
      ∑ σ : Equiv.Perm (Fin k), F (List.ofFn σ) := by
  have hnd : (List.permutations' (List.finRange k)).Nodup :=
    (List.permutations_perm_permutations' _).nodup_iff.mp
      (List.nodup_permutations _ (List.nodup_finRange k))
  rw [← List.sum_toFinset F hnd]
  have hset : (List.permutations' (List.finRange k)).toFinset =
      (Finset.univ : Finset (Equiv.Perm (Fin k))).image
        (fun σ : Equiv.Perm (Fin k) => List.ofFn σ) := by
    ext l
    rw [List.mem_toFinset, List.mem_permutations', Finset.mem_image]
    constructor
    · intro h
      obtain ⟨σ, hσ⟩ := exists_perm_ofFn_eq h
      exact ⟨σ, Finset.mem_univ σ, hσ⟩
    · rintro ⟨σ, -, rfl⟩
      exact ofFn_perm_finRange σ
  rw [hset, Finset.sum_image]
  intro σ _ τ _ h
  exact Equiv.ext (fun i => congrFun (List.ofFn_injective h) i)

/-- **Chamber pieces indexed by permutations.**  For injective `α : Fin k → ℝ^m` and any finite
`S`, there are finite sets `P σ` with `conv (P σ) = conv S ∩ {x | ⟨α (σ q), x⟩ ≤ ⟨α (σ p), x⟩ for
p < q}` and `hS S − ∑_σ hS (P σ) ∈ LSpan m (m − 1)`. -/
theorem exists_chamber_pieces (α : Fin k → Fin m → ℝ) (hα : Function.Injective α)
    (S : Finset (Fin m → ℝ)) :
    ∃ P : Equiv.Perm (Fin k) → Finset (Fin m → ℝ),
      (∀ σ : Equiv.Perm (Fin k), convexHull ℝ (P σ : Set (Fin m → ℝ)) =
        convexHull ℝ (S : Set (Fin m → ℝ)) ∩
          {x | ∀ p q : Fin k, p < q → dot (α (σ q)) x ≤ dot (α (σ p)) x}) ∧
      hS S - ∑ σ : Equiv.Perm (Fin k), hS (P σ) ∈ LSpan m (m - 1) := by
  obtain ⟨P, hP, hsum⟩ := chamber_decomp α hα (List.finRange k) (List.nodup_finRange k) S
  refine ⟨fun σ => P (List.ofFn σ), fun σ => ?_, ?_⟩
  · rw [hP (List.ofFn σ) (List.mem_permutations'.mpr (ofFn_perm_finRange σ))]
    congr 1
    ext x
    rw [mem_chamber, List.pairwise_ofFn]
    rfl
  · rw [sum_permutations'_finRange (fun l => hS (P l))] at hsum
    exact hsum

end MaxNN.ParamidGeom.Kuhn
