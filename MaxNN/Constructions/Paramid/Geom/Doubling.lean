import MaxNN.Constructions.Paramid.Geom.Defs

/-!
# Doubling of paramid units; paramid units as support functions

Module `M-Doubling` of the geometric core of `∀ n, MAX n ∈ ReLUClass n 2`
(`work/depth2_simplex/lean_core/BLUEPRINT.md`).  Source: the audit
`work/depth2_simplex/AUDIT_DEPTH_TWO_SIMPLEX_PROOF_2026-10-13.md`, Item 5, and Lemma D of
`work/depth2_simplex/EXPLICIT_CORRECTIONS_AND_TOTAL_WIDTH_2026-10-13.md` (quoted in Section 8 of
`work/depth2_simplex/CONSTRUCTIVE_SWEEP_RECONSTRUCTION_2026-10-13.md`).

Notation: `paramidOn γ V y = relu (⟨γ, y⟩ + ∑_{v ∈ V} relu ⟨v, y⟩)` for a finite set `V` of
labels, `coneVertsOn γ V = {0} ∪ {γ + ∑_{v ∈ I} v | I ⊆ V}` (both in `Geom/Defs.lean`).

* `relu_doubling_step` — the one-label identity
  `relu (C + relu b) + relu (C + b + relu b) − relu (C + b) = relu (C + 2 · relu b)`.
* `paramidOn_doubling` — **the exact doubling identity**
  `2 · paramidOn γ V =`
  `∑_{A ⊆ V} ∑_{B ⊆ V ∖ A} (−1)^{|A|} · paramidOn (2γ + ∑_{v ∈ A ∪ B} v) (V ∖ A)`.
  It is the label-by-label inclusion–exclusion `τ ∈ {0, 1, *}^V` (`A = τ⁻¹(*)`, `B = τ⁻¹(1)`).
  The `A = ∅` terms are the `2^{|V|}` cones subdividing the doubled cone; every other term has
  fewer labels (`paramidOn_doubling_sub_mem_LSpan`).
* `paramidOn_two_smul` — positive homogeneity: `paramidOn (2γ) (2V) = 2 · paramidOn γ V`.
* `paramidOn_eq_hS` — a paramid unit is the support function of its cone `coneVertsOn γ V`.
* dimension bounds: `finrank_vectorSpan_coneVertsOn_le` (`≤ |V| + 1`),
  `paramidOn_mem_LSpan`, `paramidOn_mem_LSpan_of_not_spanning` (`dim span (γ, V) ≤ k`),
  `paramidOn_mem_SSpan`.
* doubling modulo lower dimension: `paramidOn_doubling_sub_mem_LSpan`
  (`2 · paramidOn γ V − ∑_{B ⊆ V} paramidOn (2γ + ∑_B v) V ∈ LSpan m |V|`) and its reindexed
  form `paramidOn_image_doubling_sub_mem_LSpan` (labels `f r`, `r ∈ L`, `f` injective on `L`,
  sum over `B ⊆ L`: the shape of the chain doubling `S [γ; L] = ∑_{B ⊆ L} [2γ + ∑_B r; L]`).
* `paramidUnit_eq_paramidOn` — for injective labels, the `Fin k`-indexed unit of
  `Paramid/Unit.lean` is the finset-indexed one.

The scalar in `2 • γ` elaborates as a natural number (`(2 : ℕ) • γ = γ + γ`), exactly as in the
blueprint statements; `DoublingAux.dot_two_nsmul_left` evaluates it.

Helpers (linearity of `dot` in the first slot, the scalar identity behind the doubling over an
arbitrary finite label set, `LSpan` monotonicity, reindexing subsets of an injective image) live
in the namespace `MaxNN.ParamidGeom.DoublingAux`.
-/

namespace MaxNN.ParamidGeom

open BigOperators FiniteDimensional

/-! ## The one-label doubling step -/

/-- **One-label doubling step.**  For all reals `C, b`:
`relu (C + relu b) + relu (C + b + relu b) − relu (C + b) = relu (C + 2 · relu b)`.
(For `b ≥ 0` the first and third terms cancel; for `b ≤ 0` the second and third do.) -/
theorem relu_doubling_step (C b : ℝ) :
    relu (C + relu b) + relu (C + b + relu b) - relu (C + b) = relu (C + 2 * relu b) := by
  rcases le_total 0 b with hb | hb
  · rw [relu_of_nonneg hb]
    have e : C + b + b = C + 2 * b := by ring
    rw [e]
    ring
  · rw [relu_of_nonpos hb]
    simp only [add_zero, mul_zero]
    ring

namespace DoublingAux

/-! ## Helpers: linearity of `dot` in the first argument -/

theorem dot_add_left {m : ℕ} (p q y : Fin m → ℝ) : dot (p + q) y = dot p y + dot q y := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]

theorem dot_zero_left {m : ℕ} (y : Fin m → ℝ) : dot 0 y = 0 := by
  unfold dot
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Pi.zero_apply, zero_mul]

theorem dot_sum_left {m : ℕ} {ι : Type*} (s : Finset ι) (p : ι → Fin m → ℝ)
    (y : Fin m → ℝ) : dot (∑ i in s, p i) y = ∑ i in s, dot (p i) y := by
  unfold dot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_apply, Finset.sum_mul]

theorem dot_smul_left {m : ℕ} (c : ℝ) (p y : Fin m → ℝ) : dot (c • p) y = c * dot p y := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem dot_two_nsmul_left {m : ℕ} (p y : Fin m → ℝ) : dot ((2 : ℕ) • p) y = 2 * dot p y := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, two_nsmul, two_mul, add_mul]

/-- Positive homogeneity of `relu` at the scalar `2`. -/
theorem two_mul_relu (x : ℝ) : 2 * relu x = relu (2 * x) := by
  rcases le_total 0 x with h | h
  · rw [relu_of_nonneg h, relu_of_nonneg (by linarith)]
  · rw [relu_of_nonpos h, relu_of_nonpos (by linarith), mul_zero]

/-! ## The doubling identity over an arbitrary finite label set -/

/-- The doubling step in the shape needed by the induction over labels. -/
theorem doubling_combine (ε C β s₁ s₂ : ℝ) :
    ε * relu (C + 2 * relu β + s₁ + s₂) =
      ε * relu (C + s₁ + (relu β + s₂)) + ε * relu (C + (β + s₁) + (relu β + s₂)) +
        -ε * relu (C + (β + s₁) + s₂) := by
  have key := relu_doubling_step (C + s₁ + s₂) β
  have e₁ : C + 2 * relu β + s₁ + s₂ = C + s₁ + s₂ + 2 * relu β := by ring
  have e₂ : C + s₁ + (relu β + s₂) = C + s₁ + s₂ + relu β := by ring
  have e₃ : C + (β + s₁) + (relu β + s₂) = C + s₁ + s₂ + β + relu β := by ring
  have e₄ : C + (β + s₁) + s₂ = C + s₁ + s₂ + β := by ring
  rw [e₁, e₂, e₃, e₄, ← key]
  ring

/-- **Scalar doubling identity.**  For a finite label set `V`, values `b v` and an offset `C`:
`relu (C + ∑_{v ∈ V} 2 relu (b v)) =
  ∑_{A ⊆ V} ∑_{B ⊆ V ∖ A} (−1)^{|A|} relu (C + ∑_{v ∈ A ∪ B} b v + ∑_{v ∈ V ∖ A} relu (b v))`.
Induction on `V`, peeling one label with `relu_doubling_step`. -/
theorem relu_add_sum_two_mul_relu {α : Type*} [DecidableEq α] (V : Finset α) (b : α → ℝ)
    (C : ℝ) :
    relu (C + ∑ v in V, 2 * relu (b v)) =
      ∑ A in V.powerset, ∑ B in (V \ A).powerset,
        (-1 : ℝ) ^ A.card * relu (C + ∑ v in A ∪ B, b v + ∑ v in V \ A, relu (b v)) := by
  induction V using Finset.induction_on generalizing C with
  | empty =>
    simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.empty_sdiff,
      Finset.union_empty, Finset.sum_empty, Finset.card_empty, pow_zero, one_mul, add_zero]
  | @insert a s ha ih =>
    have hL : relu (C + ∑ v in insert a s, 2 * relu (b v)) =
        ∑ A in s.powerset, ∑ B in (s \ A).powerset,
          (-1 : ℝ) ^ A.card *
            relu (C + 2 * relu (b a) + ∑ v in A ∪ B, b v + ∑ v in s \ A, relu (b v)) := by
      rw [Finset.sum_insert ha, ← add_assoc]
      exact ih (C + 2 * relu (b a))
    rw [hL, Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hAs : A ⊆ s := Finset.mem_powerset.mp hA
    have haA : a ∉ A := fun h => ha (hAs h)
    have has : a ∉ s \ A := fun h => ha (Finset.mem_sdiff.mp h).1
    rw [Finset.insert_sdiff_of_not_mem s haA, Finset.sum_powerset_insert has,
      Finset.insert_sdiff_insert, Finset.sdiff_insert_of_not_mem ha,
      Finset.card_insert_of_not_mem haA, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hBs : B ⊆ s \ A := Finset.mem_powerset.mp hB
    have haB : a ∉ A ∪ B := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact haA h
      · exact has (hBs h)
    rw [Finset.union_insert, Finset.insert_union, Finset.sum_insert haB, Finset.sum_insert has,
      pow_succ, neg_one_mul]
    exact doubling_combine _ _ _ _ _

/-! ## Helpers: cones and spans -/

theorem coneVertsOn_nonempty {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    (coneVertsOn γ V).Nonempty :=
  ⟨0, Finset.mem_insert_self 0 _⟩

/-- Every vertex of the cone lies in the linear span of `γ` and the labels. -/
theorem mem_span_of_mem_coneVertsOn {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {p : Fin m → ℝ} (hp : p ∈ coneVertsOn γ V) :
    p ∈ Submodule.span ℝ (insert γ (V : Set (Fin m → ℝ))) := by
  rcases Finset.mem_insert.mp hp with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp h
    refine Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert γ _)) ?_
    refine Submodule.sum_mem _ fun v hv => Submodule.subset_span (Set.mem_insert_of_mem γ ?_)
    exact Finset.mem_coe.mpr (Finset.mem_powerset.mp hI hv)

/-- The direction of the affine span of the cone lies in `span (γ, V)`. -/
theorem vectorSpan_coneVertsOn_le {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ)) ≤
      Submodule.span ℝ (insert γ (V : Set (Fin m → ℝ))) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro x ⟨p, q, hp, hq, rfl⟩
  have h : p - q ∈ Submodule.span ℝ (insert γ (V : Set (Fin m → ℝ))) :=
    Submodule.sub_mem _ (mem_span_of_mem_coneVertsOn γ V (Finset.mem_coe.mp hp))
      (mem_span_of_mem_coneVertsOn γ V (Finset.mem_coe.mp hq))
  exact h

theorem finrank_vectorSpan_coneVertsOn_le_finrank_span {m : ℕ} (γ : Fin m → ℝ)
    (V : Finset (Fin m → ℝ)) :
    finrank ℝ (vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ))) ≤
      finrank ℝ (Submodule.span ℝ (insert γ (V : Set (Fin m → ℝ)))) :=
  Submodule.finrank_mono (vectorSpan_coneVertsOn_le γ V)

theorem finrank_span_insert_le {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    finrank ℝ (Submodule.span ℝ (insert γ (V : Set (Fin m → ℝ)))) ≤ V.card + 1 := by
  have h := finrank_span_finset_le_card (K := ℝ) (insert γ V)
  rw [Finset.coe_insert] at h
  exact le_trans h (Finset.card_insert_le γ V)

/-- `LSpan m k` is monotone in `k`. -/
theorem LSpan_mono {m k k' : ℕ} (h : k ≤ k') : LSpan m k ≤ LSpan m k' := by
  unfold LSpan
  refine Submodule.span_mono ?_
  rintro f ⟨S, hS, hdim, hf⟩
  exact ⟨S, hS, le_trans hdim h, hf⟩

/-! ## Helper: subsets of an injective image -/

theorem mem_of_image_eq_image {ι κ : Type*} [DecidableEq κ] {L : Finset ι} {f : ι → κ}
    (hf : Set.InjOn f L) {B₁ B₂ : Finset ι} (h₁ : B₁ ⊆ L) (h₂ : B₂ ⊆ L)
    (h : B₁.image f = B₂.image f) {r : ι} (hr : r ∈ B₁) : r ∈ B₂ := by
  have hfr : f r ∈ B₂.image f := h ▸ Finset.mem_image_of_mem f hr
  obtain ⟨r', hr', hr'r⟩ := Finset.mem_image.mp hfr
  have e : r' = r := hf (h₂ hr') (h₁ hr) hr'r
  rw [e] at hr'
  exact hr'

/-- For `f` injective on `L`, `B ↦ f '' B` is a bijection from the subsets of `L` onto the
subsets of `f '' L`. -/
theorem sum_powerset_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (L : Finset ι)
    (f : ι → κ) (hf : Set.InjOn f L) (G : Finset κ → ℝ) :
    ∑ B in L.powerset, G (B.image f) = ∑ B' in (L.image f).powerset, G B' := by
  refine Finset.sum_bij (fun B _ => B.image f) ?_ ?_ ?_ ?_
  · intro B hB
    exact Finset.mem_powerset.mpr (Finset.image_subset_image (Finset.mem_powerset.mp hB))
  · intro B _
    rfl
  · intro B₁ B₂ hB₁ hB₂ h
    have h₁ := Finset.mem_powerset.mp hB₁
    have h₂ := Finset.mem_powerset.mp hB₂
    ext r
    exact ⟨fun hr => mem_of_image_eq_image hf h₁ h₂ h hr,
      fun hr => mem_of_image_eq_image hf h₂ h₁ h.symm hr⟩
  · intro B' hB'
    refine ⟨L.filter (fun r => f r ∈ B'), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    ext w
    constructor
    · intro hw
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_powerset.mp hB' hw)
      exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hw⟩, rfl⟩
    · intro hw
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hr).2

end DoublingAux

open DoublingAux

/-! ## The doubling identity for paramid units -/

/-- **Positive homogeneity at `2`.**  Doubling the apex offset and every label doubles the
unit. -/
theorem paramidOn_two_smul {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (y : Fin m → ℝ) :
    paramidOn (2 • γ) (V.image (2 • ·)) y = 2 * paramidOn γ V y := by
  have hinj : ∀ p ∈ V, ∀ q ∈ V, (2 • p : Fin m → ℝ) = 2 • q → p = q := by
    intro p _ q _ h
    funext i
    have hi := congrFun h i
    rw [Pi.smul_apply, Pi.smul_apply, two_nsmul, two_nsmul] at hi
    linarith
  have hsum : ∑ w in V.image (2 • ·), relu (dot w y) = ∑ v in V, 2 * relu (dot v y) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [dot_two_nsmul_left, two_mul_relu]
  unfold paramidOn
  rw [hsum, dot_two_nsmul_left, two_mul_relu, mul_add, Finset.mul_sum]

/-- **The exact doubling identity.**
`2 · paramidOn γ V = ∑_{A ⊆ V} ∑_{B ⊆ V ∖ A} (−1)^{|A|} · paramidOn (2γ + ∑_{v ∈ A ∪ B} v) (V ∖ A)`
pointwise.  The `A = ∅` terms are the `2^{|V|}` cones over the cells
`2γ + ∑_{v ∈ B} v + ∑_{v ∈ V} [0, v]` of the doubled base; the terms with `A ≠ ∅` have fewer
labels. -/
theorem paramidOn_doubling {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (y : Fin m → ℝ) :
    2 * paramidOn γ V y = ∑ A in V.powerset, ∑ B in (V \ A).powerset,
      (-1 : ℝ) ^ A.card * paramidOn (2 • γ + ∑ v in A ∪ B, v) (V \ A) y := by
  have hL : 2 * paramidOn γ V y = relu (2 * dot γ y + ∑ v in V, 2 * relu (dot v y)) := by
    unfold paramidOn
    rw [two_mul_relu, mul_add, Finset.mul_sum]
  rw [hL, relu_add_sum_two_mul_relu V (fun v => dot v y) (2 * dot γ y)]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  unfold paramidOn
  rw [dot_add_left, dot_two_nsmul_left, dot_sum_left]

/-! ## Paramid units are support functions of cones -/

/-- **A paramid unit is the support function of its cone**: the maximum of `0` and of
`⟨γ + ∑_{v ∈ I} v, y⟩` over all `I ⊆ V`. -/
theorem paramidOn_eq_hS {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    paramidOn γ V = hS (coneVertsOn γ V) := by
  funext y
  rw [hS_of_nonempty (coneVertsOn_nonempty γ V) y]
  apply le_antisymm
  · refine max_le ?_ ?_
    · have h0 : (0 : Fin m → ℝ) ∈ coneVertsOn γ V := Finset.mem_insert_self 0 _
      calc (0 : ℝ) = dot 0 y := (dot_zero_left y).symm
        _ ≤ _ := Finset.le_sup' (fun p => dot p y) h0
    · have hI : γ + ∑ v in V.filter (fun v => 0 < dot v y), v ∈ coneVertsOn γ V := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr
          ⟨V.filter (fun v => 0 < dot v y), Finset.mem_powerset.mpr (Finset.filter_subset _ _),
            rfl⟩
      have hval : dot (γ + ∑ v in V.filter (fun v => 0 < dot v y), v) y =
          dot γ y + ∑ v in V, relu (dot v y) := by
        rw [dot_add_left, dot_sum_left, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : 0 < dot v y
        · rw [if_pos h, relu_of_nonneg h.le]
        · rw [if_neg h, relu_of_nonpos (not_lt.mp h)]
      rw [← hval]
      exact Finset.le_sup' (fun p => dot p y) hI
  · refine Finset.sup'_le _ _ fun p hp => ?_
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h, dot_zero_left]
      exact relu_nonneg _
    · obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp h
      rw [dot_add_left, dot_sum_left]
      refine le_trans ?_ (le_max_right 0 _)
      apply add_le_add_left
      calc ∑ v in I, dot v y ≤ ∑ v in I, relu (dot v y) :=
            Finset.sum_le_sum fun v _ => le_max_right 0 _
        _ ≤ ∑ v in V, relu (dot v y) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.mem_powerset.mp hI)
              fun v _ _ => relu_nonneg _

/-! ## Dimension bounds -/

/-- The cone over `γ + ∑_{v ∈ V} [0, v]` has affine dimension at most `|V| + 1`. -/
theorem finrank_vectorSpan_coneVertsOn_le {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    finrank ℝ (vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ))) ≤ V.card + 1 :=
  le_trans (finrank_vectorSpan_coneVertsOn_le_finrank_span γ V) (finrank_span_insert_le γ V)

/-- A paramid unit whose apex offset and labels span a space of dimension `≤ k` is the support
function of a point set of affine dimension `≤ k`. -/
theorem paramidOn_mem_LSpan_of_not_spanning {m k : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (h : finrank ℝ (Submodule.span ℝ (insert γ (V : Set (Fin m → ℝ)))) ≤ k) :
    paramidOn γ V ∈ LSpan m k := by
  rw [paramidOn_eq_hS]
  unfold LSpan
  exact Submodule.subset_span ⟨coneVertsOn γ V, coneVertsOn_nonempty γ V,
    le_trans (finrank_vectorSpan_coneVertsOn_le_finrank_span γ V) h,
    fun y => hS_of_nonempty (coneVertsOn_nonempty γ V) y⟩

/-- A paramid unit with label set `V` lies in `LSpan m (|V| + 1)`. -/
theorem paramidOn_mem_LSpan {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    paramidOn γ V ∈ LSpan m (V.card + 1) :=
  paramidOn_mem_LSpan_of_not_spanning γ V (finrank_span_insert_le γ V)

/-- A paramid unit lies in the span of support functions. -/
theorem paramidOn_mem_SSpan {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    paramidOn γ V ∈ SSpan m := by
  rw [paramidOn_eq_hS]
  unfold SSpan
  exact Submodule.subset_span ⟨coneVertsOn γ V, coneVertsOn_nonempty γ V, rfl⟩

/-- **Doubling modulo lower dimension.**  `2 · paramidOn γ V` minus the `2^{|V|}` cones over the
cells of the doubled base is a combination of paramid units with fewer labels, hence lies in
`LSpan m |V|`. -/
theorem paramidOn_doubling_sub_mem_LSpan {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    (fun y => 2 * paramidOn γ V y - ∑ B in V.powerset, paramidOn (2 • γ + ∑ v in B, v) V y)
      ∈ LSpan m V.card := by
  have hfun : (fun y => 2 * paramidOn γ V y -
        ∑ B in V.powerset, paramidOn (2 • γ + ∑ v in B, v) V y) =
      ∑ A in V.powerset.erase ∅, ∑ B in (V \ A).powerset,
        ((-1 : ℝ) ^ A.card) • paramidOn (2 • γ + ∑ v in A ∪ B, v) (V \ A) := by
    funext y
    rw [paramidOn_doubling, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset V)]
    simp only [Finset.sdiff_empty, Finset.empty_union, Finset.card_empty, pow_zero, one_mul,
      add_sub_cancel', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  refine Submodule.sum_mem _ fun A hA => Submodule.sum_mem _ fun B _ => Submodule.smul_mem _ _ ?_
  have hA' := Finset.mem_erase.mp hA
  have hAV : A ⊆ V := Finset.mem_powerset.mp hA'.2
  have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA'.1
  have hcard : (V \ A).card + 1 ≤ V.card := Finset.card_lt_card (Finset.sdiff_ssubset hAV hAne)
  exact LSpan_mono hcard (paramidOn_mem_LSpan _ _)

/-- **Doubling modulo lower dimension, indexed by subsets of an abstract label set.**  For labels
`f r` (`r ∈ L`, `f` injective on `L`), e.g. the root vectors of a basis chain `[γ; L]`:
`2 · paramidOn γ (f '' L) − ∑_{B ⊆ L} paramidOn (2γ + ∑_{r ∈ B} f r) (f '' L) ∈ LSpan m |L|`.
This is the shape of the chain doubling `S [γ; L] = ∑_{B ⊆ L} [2γ + ∑_{r ∈ B} r; L]`. -/
theorem paramidOn_image_doubling_sub_mem_LSpan {m : ℕ} {ι : Type*} [DecidableEq ι]
    (γ : Fin m → ℝ) (L : Finset ι) (f : ι → Fin m → ℝ) (hf : Set.InjOn f L) :
    (fun y => 2 * paramidOn γ (L.image f) y -
        ∑ B in L.powerset, paramidOn (2 • γ + ∑ r in B, f r) (L.image f) y)
      ∈ LSpan m L.card := by
  have h := paramidOn_doubling_sub_mem_LSpan γ (L.image f)
  rw [Finset.card_image_of_injOn hf] at h
  have e : (fun y => 2 * paramidOn γ (L.image f) y -
        ∑ B in L.powerset, paramidOn (2 • γ + ∑ r in B, f r) (L.image f) y) =
      (fun y => 2 * paramidOn γ (L.image f) y -
        ∑ B in (L.image f).powerset, paramidOn (2 • γ + ∑ v in B, v) (L.image f) y) := by
    funext y
    congr 1
    rw [← sum_powerset_image L f hf (fun B' => paramidOn (2 • γ + ∑ v in B', v) (L.image f) y)]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [Finset.sum_image fun r hr r' hr' h =>
      hf (Finset.mem_powerset.mp hB hr) (Finset.mem_powerset.mp hB hr') h]
  rw [e]
  exact h

/-! ## Comparison with the `Fin k`-indexed unit -/

/-- For injective labels `v : Fin k → ℝ^m`, the unit `paramidUnit γ v` of `Paramid/Unit.lean` is
`paramidOn γ` of the label set `{v₀, …, v_{k−1}}`. -/
theorem paramidUnit_eq_paramidOn {m k : ℕ} (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ)
    (hv : Function.Injective v) : paramidUnit γ v = paramidOn γ (Finset.univ.image v) := by
  funext y
  unfold paramidUnit paramidOn
  rw [Finset.sum_image fun i _ j _ h => hv h]

end MaxNN.ParamidGeom
