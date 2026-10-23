import MaxCaterpillar.CountLower

/-!
# The quadratic count for units built from arbitrary trees

A *tree face description* (class G of `research/sN/dfs/h4-trees/treeclass.py`) has an
apex `a`, a head vertex `r ≠ a`, and a spanning tree of the labels other than `a`,
rooted at `r` and given by a parent map with a strictly decreasing depth.  Every
vertex `v ∉ {a, r}` carries the edge `{v, parent v}` with a generator
`y_parent - y_v` or `y_v - y_parent` and a state: omitted, linear, or hinge.  The unit is
`σ(y_r - y_a + Σ_v edgeTerm_v(y))`, the support function of a face of the pyramid
`conv(0, e_r - e_a + Σ_v [0, g_v])`.  Caterpillars are the special case of caterpillar
trees.

The proof of `caterpillar_count_lower` uses only four facts about a unit (`Good`):
`Σ h = 0`, `h_a = -1`, the hinge pairs avoid the apex, and `|M| ≤ N - 2`.  Every tree
face function has such a description, so `N(N-1) ≤ 6|K|` for every expansion of `max_N`
by tree face functions.  (Stars attain the per-unit maximum `N - 2` of passed three-sets,
so this counting gives nothing better for trees.)
-/

open BigOperators Finset

namespace MaxCaterpillar.Trees

open MaxNN MaxNN.Width CountLower

/-- The state of a tree edge in a face: omitted, linear, or hinge. -/
inductive EdgeState
  | omit
  | linear
  | hinge
  deriving DecidableEq

/-- A face description of a pyramid over an arbitrary tree. -/
structure TreeFace (N : ℕ) where
  apex : Fin N
  root : Fin N
  parent : Fin N → Fin N
  depth : Fin N → ℕ
  /-- `true`: generator `y_parent - y_v`; `false`: generator `y_v - y_parent`. -/
  up : Fin N → Bool
  state : Fin N → EdgeState
  root_ne_apex : root ≠ apex
  parent_ne_apex : ∀ v, v ≠ apex → v ≠ root → parent v ≠ apex
  depth_lt : ∀ v, v ≠ apex → v ≠ root → depth (parent v) < depth v

namespace TreeFace

variable {N : ℕ} (F : TreeFace N)

/-- The vertices carrying a tree edge: all labels except the apex and the root. -/
def edgeVerts : Finset (Fin N) := (univ.erase F.apex).erase F.root

/-- The generator of the edge of `v` as an ordered pair `(i, j)`: `y_i - y_j`. -/
def gen (v : Fin N) : Fin N × Fin N := if F.up v then (F.parent v, v) else (v, F.parent v)

/-- The contribution of the edge of `v`. -/
noncomputable def edgeTerm (v : Fin N) (y : Fin N → ℝ) : ℝ :=
  match F.state v with
  | .omit => 0
  | .linear => y (F.gen v).1 - y (F.gen v).2
  | .hinge => MaxNN.relu (y (F.gen v).1 - y (F.gen v).2)

/-- The tree face function `σ(y_r - y_a + Σ_v edgeTerm_v(y))`. -/
noncomputable def unit (y : Fin N → ℝ) : ℝ :=
  MaxNN.relu (y F.root - y F.apex + ∑ v in F.edgeVerts, F.edgeTerm v y)

theorem mem_edgeVerts {v : Fin N} : v ∈ F.edgeVerts ↔ v ≠ F.root ∧ v ≠ F.apex := by
  unfold edgeVerts
  simp [mem_erase]

theorem parent_ne_self {v : Fin N} (hv : v ∈ F.edgeVerts) : F.parent v ≠ v := by
  rw [mem_edgeVerts] at hv
  intro h
  have := F.depth_lt v hv.2 hv.1
  rw [h] at this
  exact lt_irrefl _ this

theorem gen_ne {v : Fin N} (hv : v ∈ F.edgeVerts) : (F.gen v).1 ≠ (F.gen v).2 := by
  unfold gen
  split_ifs
  · exact F.parent_ne_self hv
  · exact (F.parent_ne_self hv).symm

theorem gen_ne_apex {v : Fin N} (hv : v ∈ F.edgeVerts) :
    (F.gen v).1 ≠ F.apex ∧ (F.gen v).2 ≠ F.apex := by
  have hv' := (F.mem_edgeVerts).mp hv
  have hp := F.parent_ne_apex v hv'.2 hv'.1
  unfold gen
  split_ifs
  · exact ⟨hp, hv'.2⟩
  · exact ⟨hv'.2, hp⟩

/-- The normalized pair `(min, max)`. -/
def normPair (p : Fin N × Fin N) : Fin N × Fin N := if p.1 < p.2 then p else (p.2, p.1)

/-- Whether the edge of `v` contributes to the head: linear, or a reversed hinge. -/
def headShift (v : Fin N) : Prop :=
  F.state v = .linear ∨ (F.state v = .hinge ∧ (F.gen v).2 < (F.gen v).1)

instance (v : Fin N) : Decidable (F.headShift v) := by unfold headShift; infer_instance

/-- The normalized description of the tree face function. -/
def descr : Descr N where
  h := fun o => ((if o = F.root then 1 else 0) - (if o = F.apex then 1 else 0)) +
    ∑ v in F.edgeVerts, (if F.headShift v then
      ((if o = (F.gen v).1 then 1 else 0) - (if o = (F.gen v).2 then 1 else 0)) else 0)
  M := (F.edgeVerts.filter fun v => F.state v = .hinge).image fun v => normPair (F.gen v)

theorem normPair_inj {u v : Fin N} (hu : u ∈ F.edgeVerts) (hv : v ∈ F.edgeVerts)
    (h : normPair (F.gen u) = normPair (F.gen v)) : u = v := by
  have hu' := (F.mem_edgeVerts).mp hu
  have hv' := (F.mem_edgeVerts).mp hv
  have du := F.depth_lt u hu'.2 hu'.1
  have dv := F.depth_lt v hv'.2 hv'.1
  -- both normalized pairs are `{u, parent u}` and `{v, parent v}`
  have key : ∀ p q : Fin N × Fin N, normPair p = normPair q →
      (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1) := by
    intro p q hpq
    unfold normPair at hpq
    split_ifs at hpq <;> simp only [Prod.mk.injEq, Prod.ext_iff] at hpq ⊢ <;> tauto
  have hk := key _ _ h
  unfold gen at hk
  by_contra hne
  split_ifs at hk <;> simp only at hk
  all_goals
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals first
    | exact hne h2 | exact hne h1 | exact hne h1.symm | exact hne h2.symm
    | (rw [h1] at du; rw [← h2] at dv; omega)
    | (rw [← h1] at dv; rw [h2] at du; omega)

theorem relu_eq_add (x : ℝ) : MaxNN.relu x = x + MaxNN.relu (-x) := by
  unfold MaxNN.relu
  rcases le_total 0 x with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem descr_arg (y : Fin N → ℝ) :
    F.descr.arg y = y F.root - y F.apex + ∑ v in F.edgeVerts, F.edgeTerm v y := by
  classical
  unfold Descr.arg descr
  simp only
  -- the linear part
  have hlin : ∑ o, (((if o = F.root then (1 : ℤ) else 0) - (if o = F.apex then 1 else 0) +
      ∑ v in F.edgeVerts, (if F.headShift v then
        ((if o = (F.gen v).1 then (1 : ℤ) else 0) - (if o = (F.gen v).2 then 1 else 0))
          else 0) : ℤ) : ℝ) * y o =
      y F.root - y F.apex + ∑ v in F.edgeVerts,
        (if F.headShift v then y (F.gen v).1 - y (F.gen v).2 else 0) := by
    push_cast
    simp only [add_mul, sub_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs
    · simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp
  -- the hinge part
  have hinj : Set.InjOn (fun v => normPair (F.gen v))
      ↑(F.edgeVerts.filter fun v => F.state v = .hinge) := by
    intro u hu v hv h
    exact F.normPair_inj (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 h
  have hhin : ∑ m in (F.edgeVerts.filter fun v => F.state v = .hinge).image
      (fun v => normPair (F.gen v)), MaxNN.relu (y m.1 - y m.2) =
      ∑ v in F.edgeVerts, (if F.state v = .hinge then
        MaxNN.relu (y (normPair (F.gen v)).1 - y (normPair (F.gen v)).2) else 0) := by
    rw [Finset.sum_image hinj, Finset.sum_filter]
  rw [hlin, hhin, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun v hv => ?_
  unfold edgeTerm headShift
  have hne := F.gen_ne hv
  have hcases : F.state v = .omit ∨ F.state v = .linear ∨ F.state v = .hinge := by
    cases F.state v <;> simp
  rcases hcases with hs | hs | hs
  · simp [hs]
  · simp [hs]
  · simp only [hs, true_and, or_false, if_true, false_or]
    unfold normPair
    have hrev := relu_eq_add (y (F.gen v).1 - y (F.gen v).2)
    split_ifs with h1 h2 h2
    · exact absurd (lt_trans h1 h2) (lt_irrefl _)
    · rw [hrev]; ring_nf
    · ring
    · exfalso
      rcases lt_trichotomy (F.gen v).1 (F.gen v).2 with h | h | h
      · exact h2 h
      · exact hne h
      · exact h1 h

theorem descr_unit (y : Fin N → ℝ) : F.descr.unit y = F.unit y := by
  unfold Descr.unit unit
  rw [descr_arg]

theorem descr_good (hN : 2 ≤ N) : Good F.descr F.apex := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Σ h = 0`
    show ∑ o, (((if o = F.root then (1 : ℤ) else 0) - (if o = F.apex then 1 else 0)) +
      ∑ v in F.edgeVerts, (if F.headShift v then
        ((if o = (F.gen v).1 then 1 else 0) - (if o = (F.gen v).2 then 1 else 0)) else 0)) = 0
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self, zero_add]
    refine Finset.sum_eq_zero fun v _ => ?_
    split_ifs
    · rw [Finset.sum_sub_distrib]
      simp
    · simp
  · -- `h_a = -1`
    show ((if F.apex = F.root then (1 : ℤ) else 0) - (if F.apex = F.apex then 1 else 0)) +
      ∑ v in F.edgeVerts, (if F.headShift v then
        ((if F.apex = (F.gen v).1 then 1 else 0) - (if F.apex = (F.gen v).2 then 1 else 0))
          else 0) = -1
    rw [if_neg F.root_ne_apex.symm, if_pos rfl]
    rw [Finset.sum_eq_zero fun v hv => by
      have := F.gen_ne_apex hv
      rw [if_neg (Ne.symm this.1), if_neg (Ne.symm this.2)]
      simp]
    norm_num
  · -- pairs are ordered and avoid the apex
    intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    have hv1 := (Finset.mem_filter.mp hv).1
    have hne := F.gen_ne hv1
    have hap := F.gen_ne_apex hv1
    unfold normPair
    split_ifs with h
    · exact ⟨h, hap.1, hap.2⟩
    · refine ⟨?_, hap.2, hap.1⟩
      rcases lt_trichotomy (F.gen v).1 (F.gen v).2 with h' | h' | h'
      · exact absurd h' h
      · exact absurd h' hne
      · exact h'
  · -- `|M| + 2 ≤ N`
    show ((F.edgeVerts.filter fun v => F.state v = .hinge).image
      fun v => normPair (F.gen v)).card + 2 ≤ N
    have h3 : F.edgeVerts.card = N - 2 := by
      unfold edgeVerts
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨F.root_ne_apex, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      rfl
    refine le_trans (Nat.add_le_add_right (Finset.card_image_le.trans
      ((Finset.card_filter_le _ _).trans h3.le)) 2) ?_
    omega

end TreeFace

/-! ## The count -/

/-- `C(N,3) ≤ |K| (N - 2)` for every expansion by functions with a `Good` description. -/
theorem choose_three_le_of_good (r : ℕ) {ι : Type*} (K : Finset ι)
    (U : ι → (Fin (r + 1 + 1) → ℝ) → ℝ)
    (hU : ∀ i ∈ K, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, U i y = D.unit y)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * U k x + auxiliary a x) :
    (r + 1 + 1).choose 3 ≤ K.card * r := by
  classical
  haveI : Inhabited (Descr (r + 1 + 1)) := ⟨⟨0, ∅⟩⟩
  have hU' : ∀ i, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      i ∈ K → Good D apex ∧ ∀ y, U i y = D.unit y := by
    intro i
    by_cases hi : i ∈ K
    · obtain ⟨D, apex, hD⟩ := hU i hi
      exact ⟨D, apex, fun _ => hD⟩
    · exact ⟨⟨0, ∅⟩, 0, fun h => absurd h hi⟩
  choose D apex hDU using hU'
  have hgood : ∀ k ∈ K, Good (D k) (apex k) := fun k hk => (hDU k hk).1
  have hunit : ∀ k ∈ K, ∀ y, U k y = (D k).unit y := fun k hk => (hDU k hk).2
  let B : ℕ := 2 + ∑ k in K, (∑ o, ((D k).h o).natAbs + (D k).M.card)
  let S : ℝ := ∑ k in K, (∑ o, |((D k).h o : ℝ)| + 4 * (D k).M.card)
  let η : ℝ := 1 / (3 * (1 + S))
  have hSk : ∀ k ∈ K, 0 ≤ ∑ o, |((D k).h o : ℝ)| + 4 * ((D k).M.card : ℝ) := fun k _ =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _) (by positivity)
  have hS0 : 0 ≤ S := Finset.sum_nonneg hSk
  have hη : 0 < η := by positivity
  have hη3 : 3 * η = 1 / (1 + S) := by
    show (3 : ℝ) * (1 / (3 * (1 + S))) = 1 / (1 + S)
    rw [mul_one_div, ← div_div, div_self (by norm_num : (3 : ℝ) ≠ 0)]
  have hη1 : 3 * η ≤ 1 := by
    rw [hη3, div_le_one (by linarith)]
    linarith
  have hB2 : 2 ≤ B := Nat.le_add_right 2 _
  have hBk : ∀ k ∈ K, ∑ o, |(D k).h o| + ((D k).M.card : ℤ) < (B : ℤ) := by
    intro k hk
    have h1 : ∑ o, |(D k).h o| + ((D k).M.card : ℤ) =
        ((∑ o, ((D k).h o).natAbs + (D k).M.card : ℕ) : ℤ) := by
      push_cast
      simp only [Int.coe_natAbs]
    have h2 : ∑ o, ((D k).h o).natAbs + (D k).M.card ≤
        ∑ k in K, (∑ o, ((D k).h o).natAbs + (D k).M.card) :=
      Finset.single_le_sum (f := fun k => ∑ o, ((D k).h o).natAbs + (D k).M.card)
        (fun _ _ => Nat.zero_le _) hk
    rw [h1]
    have : ∑ o, ((D k).h o).natAbs + (D k).M.card < B := by
      simp only [B]
      omega
    exact_mod_cast this
  have hbdk : ∀ k ∈ K,
      3 * η * (∑ o, |((D k).h o : ℝ)| + 4 * (D k).M.card) ≤ 1 := by
    intro k hk
    have h1 : ∑ o, |((D k).h o : ℝ)| + 4 * ((D k).M.card : ℝ) ≤ S :=
      Finset.single_le_sum (f := fun k => ∑ o, |((D k).h o : ℝ)| + 4 * ((D k).M.card : ℝ))
        hSk hk
    rw [hη3, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  have hcover : Finset.powersetCard 3 (Finset.univ : Finset (Fin (r + 1 + 1))) ⊆
      K.biUnion fun k => allowed (D k) (apex k) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨p, q, c, hpq, hpc, hqc, hTe⟩ := Finset.card_eq_three.mp hT.2
    have hp : p ∈ T := by rw [hTe]; simp
    have hq : q ∈ T := by rw [hTe]; simp
    have hc : c ∈ T := by rw [hTe]; simp
    have hsplit : Λ T B p q η (MAX (r + 1 + 1)) =
        ∑ k in K, d k * Λ T B p q η (U k) +
          Λ T B p q η (fun x => ∑ j, a j * feat (r + 1 + 1) x j) := by
      unfold Λ
      have e : (fun α β => MAX (r + 1 + 1) (pt T B p q α β)) = fun α β =>
          (∑ k in K, (fun k α β => d k * U k (pt T B p q α β)) k α β) +
            (fun x => ∑ j, a j * feat (r + 1 + 1) x j) (pt T B p q α β) := by
        funext α β
        exact h _
      rw [e, Φ_add, Φ_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => Φ_mul η (d k) _
    rw [Λ_MAX hη.le hp hq hc hpq (Ne.symm hpc) (Ne.symm hqc),
      Λ_auxiliary hη.le hη1 hB2 hp hq hpq, add_zero] at hsplit
    have hne : ∑ k in K, d k * Λ T B p q η (U k) ≠ 0 := by
      rw [← hsplit]
      exact (mul_pos two_pos hη).ne'
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hUk : Λ T B p q η (D k).unit ≠ 0 := by
      have e : U k = (D k).unit := funext (hunit k hk)
      rw [← e]
      exact right_ne_zero_of_mul hk0
    have hpass := pass_of_Λ_unit_ne (D k) hη hη1 hB2 hp hq hpq (hbdk k hk) hUk
    exact Finset.mem_biUnion.mpr
      ⟨k, hk, mem_allowed (hgood k hk) hTe hpq hpc hqc (hBk k hk) hpass⟩
  have h1 := Finset.card_le_of_subset hcover
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
  calc (r + 1 + 1).choose 3 ≤ (K.biUnion fun k => allowed (D k) (apex k)).card := h1
    _ ≤ ∑ k in K, (allowed (D k) (apex k)).card := Finset.card_biUnion_le
    _ ≤ ∑ _k in K, r := Finset.sum_le_sum fun k hk => by
        have := card_allowed (hgood k hk)
        simpa using this
    _ = K.card * r := by rw [Finset.sum_const, smul_eq_mul]

/-- `N(N-1) ≤ 6|K|` for every expansion by functions with a `Good` description. -/
theorem count_lower_of_good (r : ℕ) (hr : 1 ≤ r) {ι : Type*} (K : Finset ι)
    (U : ι → (Fin (r + 1 + 1) → ℝ) → ℝ)
    (hU : ∀ i ∈ K, ∃ (D : Descr (r + 1 + 1)) (apex : Fin (r + 1 + 1)),
      Good D apex ∧ ∀ y, U i y = D.unit y)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ k in K, d k * U k x + auxiliary a x) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card := by
  have h3 := choose_three_le_of_good r K U hU d a h
  have hdesc : (r + 1 + 1).descFactorial 3 = (r + 1 + 1) * (r + 1) * r := by
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_one]
    ring
  have hfac : (r + 1 + 1).descFactorial 3 = 6 * (r + 1 + 1).choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h6 : (r + 1 + 1) * (r + 1) * r ≤ 6 * K.card * r := by
    rw [← hdesc, hfac, mul_assoc]
    exact Nat.mul_le_mul_left 6 h3
  exact le_of_mul_le_mul_right h6 (by omega)

/-! ## Public statement -/

/-- `K` is a tree expansion of the maximum: `max_N = Σ_{F ∈ K} d_F U_F + (auxiliary)`,
with `U_F` the face function of a pyramid over an arbitrary tree. -/
def IsTreeExpansion (r : ℕ) (K : Finset (TreeFace (r + 1 + 1))) : Prop :=
  ∃ (d : TreeFace (r + 1 + 1) → ℝ) (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
    ∀ x, Maximum (r + 1 + 1) x =
      ∑ F in K, d F * F.unit x + ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

/-- **Quadratic count for arbitrary trees.** Every expansion of `max_N`, `N = r + 2 ≥ 3`,
by face functions of pyramids over arbitrary trees uses `N(N-1) ≤ 6|K|` of them. -/
theorem tree_expansion_quadratic (r : ℕ) (hr : 1 ≤ r) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card := by
  obtain ⟨d, a, h⟩ := hK
  refine count_lower_of_good r hr K (fun F => F.unit) (fun F _ => ?_) d a h
  exact ⟨F.descr, F.apex, F.descr_good (by omega), fun y => (F.descr_unit y).symm⟩

end MaxCaterpillar.Trees
