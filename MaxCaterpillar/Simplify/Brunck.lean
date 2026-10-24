import MaxCaterpillar.Simplify.TreeUnits
import MaxCaterpillar.Audit.CaterpillarTree

/-!
# Caterpillars and the rooted stars of Brunck et al., all counted, base 6

The vocabulary of Brunck–Hertrich–Rueß–Stade–Yehudayoff (Sec. 7.1): pyramids over
`B_{v,π,M}`; for `M ≠ ∅` the caterpillar polytopes, for `M = ∅` the rooted stars.  Their
face functions: the caterpillar functions `U_k`, `k ∈ 𝒦₀`, and the faces of the rooted
stars `σ(x_c - x_a + Σ_l t_l)`, `t_l ∈ {0, x_c - x_l, σ(x_c - x_l)}` (`IsStarFace`).

`brunck_expansion_choose_le`: every expansion
`max_N = Σ_{k ∈ K₁} d_k U_k + Σ_{F ∈ K₂} e_F U_F + (auxiliary)` has
`C(N, m) ≤ 6^m (|K₁| + |K₂|)` for `3 ≤ m ≤ N`, and `brunck_expansion_exponential`:
`7^N ≤ (N+1) 6^N (|K₁| + |K₂|)`.

Every caterpillar function is the face function of a caterpillar tree whose leaves carry
`x_parent - x_leaf` (`caterpillarFunction_eq_upTree`, from the tree of
`Audit.treeFaceOf`), so it has reduced degree `≤ 2`; rooted-star faces have reduced
degree `0`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Simplify

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower CountExp Trees Audit

variable {r : ℕ}

/-- The caterpillar tree of a word has upward leaves. -/
theorem treeFaceOf_isUpCaterpillar (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    TreeFaceR.IsUpCaterpillar (treeFaceOf w τ) := by
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
    ∃ F : TreeFace (r + 1 + 1), TreeFaceR.IsUpCaterpillar F ∧ caterpillarFunction k = F.unit := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hqc
  refine ⟨treeFaceOf w τ, treeFaceOf_isUpCaterpillar w τ, ?_⟩
  unfold caterpillarFunction
  rw [realUnitY_normalizedKey hq]
  funext y
  exact realUnitY_faceKey w τ y

/-- An expansion of `max_N` by caterpillar functions (`K₁`) and rooted-star faces (`K₂`). -/
def IsBrunckExpansion (r : ℕ) (K₁ : Finset (FaceKey r)) (K₂ : Finset (TreeFace (r + 1 + 1))) :
    Prop :=
  K₁ ⊆ caterpillarDescriptions r ∧ (∀ F ∈ K₂, TreeFaceR.IsStarFace F) ∧
    ∃ (d₁ : FaceKey r → ℝ) (d₂ : TreeFace (r + 1 + 1) → ℝ)
      (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in K₁, d₁ k * caterpillarFunction k x + ∑ F in K₂, d₂ F * F.unit x +
          ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

/-- **Binomial count for caterpillars and rooted stars, all counted.** -/
theorem brunck_expansion_choose_le {K₁ : Finset (FaceKey r)} {K₂ : Finset (TreeFace (r + 1 + 1))}
    (hK : IsBrunckExpansion r K₁ K₂) {m : ℕ} (hm : 3 ≤ m) (hmN : m ≤ r + 1 + 1) :
    (r + 1 + 1).choose m ≤ 6 ^ m * (K₁.card + K₂.card) := by
  classical
  obtain ⟨hsub, hstar, d₁, d₂, a, h⟩ := hK
  have hex : ∀ k : FaceKey r, ∃ F : TreeFace (r + 1 + 1),
      (k ∈ caterpillarDescriptions r → TreeFaceR.IsUpCaterpillar F ∧ caterpillarFunction k = F.unit) := by
    intro k
    by_cases hk : k ∈ caterpillarDescriptions r
    · obtain ⟨F, hF, he⟩ := caterpillarFunction_eq_upTree hk
      exact ⟨F, fun _ => ⟨hF, he⟩⟩
    · exact ⟨Trees.starFace 0 1 (by simp), fun h => absurd h hk⟩
  choose f hf using hex
  set K : Finset (FaceKey r ⊕ TreeFace (r + 1 + 1)) := K₁.disjSum K₂
  set D : FaceKey r ⊕ TreeFace (r + 1 + 1) → Descr (r + 1 + 1) :=
    fun i => Sum.elim (fun k => (f k).descr) (fun F => F.descr) i
  set dd : FaceKey r ⊕ TreeFace (r + 1 + 1) → ℝ := Sum.elim d₁ d₂
  have hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2 := by
    intro i _
    cases i with
    | inl k => exact (f k).descr_lt
    | inr F => exact F.descr_lt
  have hleaf : ∀ i ∈ K, LeafProp (D i).M := by
    intro i _
    cases i with
    | inl k => exact (f k).descr_leaf
    | inr F => exact F.descr_leaf
  have hred : ∀ i ∈ K, RedDeg (D i) 2 := by
    intro i hi
    cases i with
    | inl k =>
      have hk : k ∈ K₁ := by simpa [K] using hi
      exact TreeFaceR.redDeg_of_isUpCaterpillar _ (hf k (hsub hk)).1
    | inr F =>
      have hF : F ∈ K₂ := by simpa [K] using hi
      exact TreeFaceR.redDeg_of_isStar _ (hstar F hF) 2
  have hexp : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, dd i * (D i).unit x + auxiliary a x := by
    intro x
    rw [h x, sum_disj_sum]
    simp only [dd, D, Sum.elim_inl, Sum.elim_inr, TreeFace.descr_unit]
    congr 2
    refine sum_congr rfl fun k hk => ?_
    rw [(hf k (hsub hk)).2]
  have := choose_le_of_red r K D hlt hleaf le_rfl hred dd a hexp hm hmN
  simpa [K] using this

/-- **Exponential count for caterpillars and rooted stars, all counted.** For `N ≥ 3`,
`7^N ≤ (N+1) 6^N (|K₁| + |K₂|)`, i.e. `|K₁| + |K₂| ≥ (7/6)^N/(N+1)`. -/
theorem brunck_expansion_exponential (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsBrunckExpansion r K₁ K₂) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * (K₁.card + K₂.card) :=
  seven_pow_le_of_choose_le' (by omega) fun _m hm hmN => brunck_expansion_choose_le hK hm hmN

end MaxCaterpillar.Simplify
