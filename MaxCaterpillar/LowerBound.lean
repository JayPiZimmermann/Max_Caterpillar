import MaxCaterpillar.Quotient

/-! # A vocabulary-dimension lower bound: `q_N ≥ (N - 2)!`

Consider the all-cut paths with apex label `0` and last spine label
`b = N - 1`, one for every order of the remaining `N - 2` labels.  Vary
`x_0 = 1 + t`, put `x_b = 1`, and place the other coordinates either at
`(position in a path)/(N - 1) ∈ (0, 1)` (test configuration of that path) or
at `2` (reference configuration).  The symmetric second difference

  `J f = f(x + ε e_0) + f(x - ε e_0) - 2 f(x)`,

taken at the test configuration minus the reference configuration, vanishes
on every auxiliary function.  On path units it equals `ε` for the matching
path and `0` otherwise: the matching path has outer behaviour `σ(-t)`, and
every other path has a positive inner hinge, hence is affine near `t = 0`.
Thus the path units are independent modulo `A_N`.

Scope: this bounds the dimension `q_N` of the vocabulary quotient.  It is not
a lower bound on the number of units needed to represent the maximum, and not
a lower bound for unrestricted ReLU networks.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom ParamidChain

variable {r : ℕ}

/-! ## Second differences of a ReLU along one direction -/

/-- The step `ε = 1 / (2 (N - 1))`. -/
noncomputable def step (r : ℕ) : ℝ := 1 / (2 * ((r : ℝ) + 1))

theorem step_pos (r : ℕ) : 0 < step r := by
  unfold step
  positivity

theorem two_step (r : ℕ) : 2 * step r = 1 / ((r : ℝ) + 1) := by
  unfold step; field_simp

theorem step_le_one (r : ℕ) : step r ≤ 1 := by
  unfold step
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  linarith

/-- `relu (a + e c) + relu (a - e c) - 2 relu a` when the kink is at `a = 0`
or outside the segment. -/
theorem relu_jump {a c e : ℝ} (he : 0 ≤ e) (h : a = 0 ∨ e * |c| ≤ |a|) :
    relu (a + e * c) + relu (a + -e * c) - 2 * relu a = if a = 0 then e * |c| else 0 := by
  have hm : |e * c| = e * |c| := by rw [abs_mul, abs_of_nonneg he]
  have h1 := le_abs_self (e * c)
  have h2 := neg_abs_le_self (e * c)
  unfold relu
  by_cases ha : a = 0
  · rw [if_pos ha, ha, max_self, ← hm]
    rcases le_total 0 (e * c) with hc | hc
    · rw [abs_of_nonneg hc, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos hc, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [if_neg ha]
    have hle : |e * c| ≤ |a| := by
      rcases h with h | h
      · exact absurd h ha
      · rw [hm]; exact h
    rcases lt_or_gt_of_ne ha with hn | hp
    · rw [abs_of_neg hn] at hle
      rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left hn.le]; ring
    · rw [abs_of_pos hp] at hle
      rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right hp.le]; ring

/-! ## Configurations -/

/-- Coordinate `0` is `1 + t`; every other coordinate is `w i`. -/
noncomputable def cfg (w : Point (r + 1 + 1)) (t : ℝ) : Point (r + 1 + 1) :=
  fun i => if i = 0 then 1 + t else w i

/-- The second difference of `g` at `cfg w` in direction `e_0`. -/
noncomputable def jump (w : Point (r + 1 + 1)) (g : Point (r + 1 + 1) → ℝ) : ℝ :=
  g (cfg w (step r)) + g (cfg w (-step r)) - 2 * g (cfg w 0)

theorem cfg_zero (w : Point (r + 1 + 1)) (t : ℝ) : cfg w t 0 = 1 + t := if_pos rfl

theorem cfg_ne {w : Point (r + 1 + 1)} {i : Fin (r + 1 + 1)} (hi : i ≠ 0) (t : ℝ) :
    cfg w t i = w i := if_neg hi

/-- Separation: away from coordinate `0`, `w` equals `1` or stays `2 ε` away. -/
def Separated (w : Point (r + 1 + 1)) : Prop :=
  ∀ i, i ≠ 0 → w i = 1 ∨ 2 * step r ≤ |w i - 1|

theorem jump_const {w : Point (r + 1 + 1)} {g : Point (r + 1 + 1) → ℝ}
    (h : ∀ t, g (cfg w t) = g (cfg w 0)) : jump w g = 0 := by
  unfold jump; rw [h, h (-step r)]; ring

/-- Second difference of `σ(A + t c)`. -/
theorem jump_relu {w : Point (r + 1 + 1)} {g : Point (r + 1 + 1) → ℝ} {A c : ℝ}
    (hg : ∀ t, g (cfg w t) = relu (A + t * c)) (h : A = 0 ∨ step r * |c| ≤ |A|) :
    jump w g = if A = 0 then step r * |c| else 0 := by
  unfold jump
  rw [hg, hg, hg, zero_mul, add_zero, ← relu_jump (step_pos r).le h]

theorem jump_relu_coord {w : Point (r + 1 + 1)} (i : Fin (r + 1 + 1)) (σ : ℝ) (hσ : |σ| = 1) :
    jump w (fun x => relu (σ * x i)) = 0 := by
  by_cases hi : i = 0
  · subst hi
    have h := jump_relu (w := w) (g := fun x => relu (σ * x 0)) (A := σ) (c := σ)
      (fun t => by simp only [cfg_zero]; ring_nf) (Or.inr (by rw [hσ]; linarith [step_le_one r]))
    rw [h, if_neg (by intro h0; rw [h0, abs_zero] at hσ; exact zero_ne_one hσ)]
  · exact jump_const fun t => by simp only [cfg_ne hi]

/-- The second difference of `σ(x_a - x_c)`, `a ≠ c`. -/
theorem jump_relu_pair {w : Point (r + 1 + 1)} (hw : Separated w) {a c : Fin (r + 1 + 1)}
    (hac : a ≠ c) :
    jump w (fun x => relu (x a - x c)) =
      if (a = 0 ∧ w c = 1) ∨ (c = 0 ∧ w a = 1) then step r else 0 := by
  by_cases ha : a = 0
  · subst ha
    have hc : c ≠ 0 := Ne.symm hac
    have h := jump_relu (w := w) (g := fun x => relu (x 0 - x c)) (A := 1 - w c) (c := 1)
      (fun t => by simp only [cfg_zero, cfg_ne hc]; ring_nf)
      (by
        rcases hw c hc with h1 | h2
        · left; rw [h1]; ring
        · right; rw [abs_one, mul_one, abs_sub_comm]; linarith [step_pos r])
    rw [h, abs_one, mul_one]
    by_cases hwc : w c = 1
    · rw [if_pos (by rw [hwc]; ring), if_pos (Or.inl ⟨rfl, hwc⟩)]
    · rw [if_neg (by intro h0; apply hwc; linarith), if_neg]
      rintro (⟨-, h1⟩ | ⟨h1, -⟩)
      · exact hwc h1
      · exact hc h1
  · by_cases hc : c = 0
    · subst hc
      have h := jump_relu (w := w) (g := fun x => relu (x a - x 0)) (A := w a - 1) (c := -1)
        (fun t => by simp only [cfg_zero, cfg_ne ha]; ring_nf)
        (by
          rcases hw a ha with h1 | h2
          · left; rw [h1]; ring
          · right; rw [abs_neg, abs_one, mul_one]; linarith [step_pos r])
      rw [h, abs_neg, abs_one, mul_one]
      by_cases hwa : w a = 1
      · rw [if_pos (by rw [hwa]; ring), if_pos (Or.inr ⟨rfl, hwa⟩)]
      · rw [if_neg (by intro h0; apply hwa; linarith), if_neg]
        rintro (⟨h1, -⟩ | ⟨-, h1⟩)
        · exact ha h1
        · exact hwa h1
    · rw [if_neg (by rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> contradiction)]
      exact jump_const fun t => by simp only [cfg_ne ha, cfg_ne hc]

/-- The second difference of every auxiliary function depends only on which
coordinates other than `0` equal `1`. -/
theorem jump_feat_eq {w w' : Point (r + 1 + 1)} (hw : Separated w) (hw' : Separated w')
    (hiff : ∀ i, i ≠ 0 → (w i = 1 ↔ w' i = 1)) (j : Fin (W (r + 1 + 1))) :
    jump w (fun x => feat (r + 1 + 1) x j) = jump w' (fun x => feat (r + 1 + 1) x j) := by
  refine Fin.addCases (motive := fun j : Fin ((r + 1 + 1) + ((r + 1 + 1) +
      (r + 1 + 1).choose 2)) => jump w (fun x => feat (r + 1 + 1) x j) =
        jump w' (fun x => feat (r + 1 + 1) x j)) (fun i => ?_) (fun j => ?_) j
  · have h : (fun x : Point (r + 1 + 1) => feat (r + 1 + 1) x (Fin.castAdd _ i)) =
        fun x => relu (1 * x i) := funext fun x => by
      rw [one_mul]; exact feat_pos x i
    show jump w (fun x => feat (r + 1 + 1) x (Fin.castAdd _ i)) =
      jump w' (fun x => feat (r + 1 + 1) x (Fin.castAdd _ i))
    rw [h, jump_relu_coord i 1 abs_one, jump_relu_coord i 1 abs_one]
  · refine Fin.addCases (motive := fun j : Fin ((r + 1 + 1) + (r + 1 + 1).choose 2) =>
      jump w (fun x => feat (r + 1 + 1) x (Fin.natAdd _ j)) =
        jump w' (fun x => feat (r + 1 + 1) x (Fin.natAdd _ j))) (fun i => ?_) (fun q => ?_) j
    · have h : (fun x : Point (r + 1 + 1) => feat (r + 1 + 1) x
          (Fin.natAdd _ (Fin.castAdd _ i))) = fun x => relu (-1 * x i) := funext fun x => by
        rw [neg_one_mul]; exact feat_neg x i
      show jump w (fun x => feat (r + 1 + 1) x (Fin.natAdd _ (Fin.castAdd _ i))) =
        jump w' (fun x => feat (r + 1 + 1) x (Fin.natAdd _ (Fin.castAdd _ i)))
      rw [h, jump_relu_coord i (-1) (by rw [abs_neg, abs_one]),
        jump_relu_coord i (-1) (by rw [abs_neg, abs_one])]
    · have h : (fun x : Point (r + 1 + 1) => feat (r + 1 + 1) x
          (Fin.natAdd _ (Fin.natAdd _ q))) = fun x => relu (x (prFst q) - x (prSnd q)) :=
        funext fun x => feat_pr x q
      have hne : prFst q ≠ prSnd q := ne_of_lt (prFst_lt_prSnd q)
      show jump w (fun x => feat (r + 1 + 1) x (Fin.natAdd _ (Fin.natAdd _ q))) =
        jump w' (fun x => feat (r + 1 + 1) x (Fin.natAdd _ (Fin.natAdd _ q)))
      rw [h, jump_relu_pair hw hne, jump_relu_pair hw' hne]
      refine if_congr ?_ rfl rfl
      constructor <;> rintro (⟨h0, h⟩ | ⟨h1, h⟩)
      · exact Or.inl ⟨h0, (hiff _ (fun hc => hne (h0.trans hc.symm))).mp h⟩
      · exact Or.inr ⟨h1, (hiff _ (fun hc => hne (hc.trans h1.symm))).mp h⟩
      · exact Or.inl ⟨h0, (hiff _ (fun hc => hne (h0.trans hc.symm))).mpr h⟩
      · exact Or.inr ⟨h1, (hiff _ (fun hc => hne (hc.trans h1.symm))).mpr h⟩

/-! ## Path units -/

/-- Labels other than the apex label `0` and the endpoint `b = N - 1`. -/
def Middle (r : ℕ) (a : Fin (r + 1 + 1)) : Prop := a ≠ 0 ∧ a ≠ Fin.last (r + 1)

instance (r : ℕ) : DecidablePred (Middle r) := fun _ => instDecidableAnd

/-- Orders of the middle labels: permutations fixing `0` and `b`. -/
abbrev PathIdx (r : ℕ) :=
  {π : Equiv.Perm (Fin (r + 1 + 1)) // ∀ a, ¬ Middle r a → π a = a}

theorem PathIdx.map_zero (π : PathIdx r) : π.1 0 = 0 := π.2 0 fun h => h.1 rfl

theorem PathIdx.map_last (π : PathIdx r) : π.1 (Fin.last (r + 1)) = Fin.last (r + 1) :=
  π.2 _ fun h => h.2 rfl

theorem PathIdx.ne_zero (π : PathIdx r) {a : Fin (r + 1 + 1)} (ha : a ≠ 0) : π.1 a ≠ 0 :=
  fun h => ha (π.1.injective (h.trans π.map_zero.symm))

theorem PathIdx.ne_last (π : PathIdx r) {a : Fin (r + 1 + 1)} (ha : a ≠ Fin.last (r + 1)) :
    π.1 a ≠ Fin.last (r + 1) :=
  fun h => ha (π.1.injective (h.trans π.map_last.symm))

theorem PathIdx.symm_last (π : PathIdx r) : π.1.symm (Fin.last (r + 1)) = Fin.last (r + 1) := by
  rw [Equiv.symm_apply_eq]; exact π.map_last.symm

theorem PathIdx.symm_ne_zero (π : PathIdx r) {a : Fin (r + 1 + 1)} (ha : a ≠ 0) :
    π.1.symm a ≠ 0 := by
  intro h
  rw [Equiv.symm_apply_eq, π.map_zero] at h
  exact ha h

theorem PathIdx.symm_ne_last (π : PathIdx r) {a : Fin (r + 1 + 1)}
    (ha : a ≠ Fin.last (r + 1)) : π.1.symm a ≠ Fin.last (r + 1) := by
  intro h
  rw [Equiv.symm_apply_eq, π.map_last] at h
  exact ha h

theorem card_pathIdx (r : ℕ) : Fintype.card (PathIdx r) = r.factorial := by
  classical
  rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (Middle r)),
    Fintype.card_perm, Fintype.card_subtype]
  have h : Finset.univ.filter (Middle r) = (Finset.univ.erase 0).erase (Fin.last (r + 1)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Middle, and_true]
    exact and_comm
  have hl : Fin.last (r + 1) ∈ Finset.univ.erase (0 : Fin (r + 1 + 1)) :=
    Finset.mem_erase.mpr ⟨fun h => by have := congrArg Fin.val h; simp at this,
      Finset.mem_univ _⟩
  rw [h, Finset.card_erase_of_mem hl, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  rfl

/-- The all-cut path unit of a label order `π`. -/
noncomputable def pathUnit (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    Point (r + 1 + 1) → ℝ :=
  realUnitY (wordKey (pathWord hr π))

theorem pathUnit_apply (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r + 1 + 1)))
    (x : Point (r + 1 + 1)) :
    pathUnit hr π x = relu (x (π (Fin.last (r + 1))) - x (π 0) +
      ∑ j : Fin r, relu (x (π j.castSucc.succ) - x (π j.succ.succ))) := by
  classical
  have hinj : Function.Injective (edgeVecs (wordBase (pathWord hr π)) (cutPositions r)) :=
    edgeVecs_simplex_injective (fun i => π i.succ)
      (π.injective.comp (Fin.succ_injective (r + 1))) (cutPositions r)
  unfold pathUnit
  rw [realUnitY_eq_relu]
  unfold realUnitArg
  congr 1
  change dot (wordBase (pathWord hr π) (lastHead (cutPositions r)) -
      wordApex (pathWord hr π)) _ + ∑ v in Finset.univ.image
        (edgeVecs (wordBase (pathWord hr π)) (cutPositions r)), relu (dot v _) = _
  rw [Finset.sum_image (fun a _ b _ he => hinj he), lastHead_cutPositions hr]
  congr 1
  · unfold wordBase wordApex pathWord
    dsimp only
    rw [SupportCut.dot_sub_left, dot_toR_vtx_coordT, dot_toR_vtx_coordT, Fin.succ_last]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold edgeVecs wordBase pathWord
    dsimp only
    rw [parent_cutPositions_succ, SupportCut.dot_sub_left, dot_toR_vtx_coordT,
      dot_toR_vtx_coordT]
    congr 1
    ring

theorem pathUnit_mem (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    pathUnit hr π ∈ vocabularySpan r := by
  apply Submodule.subset_span
  rw [dictionary_eq_range]
  exact ⟨Sum.inl ⟨wordKey (pathWord hr π),
    faceKeys_subset_correctionKeys _ (self_mem_faceKeys _ _)⟩, rfl⟩

/-- The inner hinge sum of a path at the values `w`. -/
noncomputable def pathSum (π : Equiv.Perm (Fin (r + 1 + 1))) (w : Point (r + 1 + 1)) : ℝ :=
  ∑ j : Fin r, relu (w (π j.castSucc.succ) - w (π j.succ.succ))

theorem pathSum_nonneg (π : Equiv.Perm (Fin (r + 1 + 1))) (w : Point (r + 1 + 1)) :
    0 ≤ pathSum π w :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

theorem last_ne_zero' : Fin.last (r + 1) ≠ (0 : Fin (r + 1 + 1)) := by
  intro h; have := congrArg Fin.val h; simp at this

theorem pathUnit_cfg (hr : 1 ≤ r) (σ : PathIdx r) {w : Point (r + 1 + 1)}
    (hw : w (Fin.last (r + 1)) = 1) (t : ℝ) :
    pathUnit hr σ.1 (cfg w t) = relu (pathSum σ.1 w + t * -1) := by
  rw [pathUnit_apply, σ.map_last, σ.map_zero, cfg_zero, cfg_ne last_ne_zero', hw]
  unfold pathSum
  rw [Finset.sum_congr rfl fun j _ => by
    rw [cfg_ne (σ.ne_zero (Fin.succ_ne_zero _)), cfg_ne (σ.ne_zero (Fin.succ_ne_zero _))]]
  congr 1
  ring

theorem jump_pathUnit (hr : 1 ≤ r) (σ : PathIdx r) {w : Point (r + 1 + 1)}
    (hw : w (Fin.last (r + 1)) = 1) (hsep : pathSum σ.1 w = 0 ∨ step r ≤ pathSum σ.1 w) :
    jump w (pathUnit hr σ.1) = if pathSum σ.1 w = 0 then step r else 0 := by
  rw [jump_relu (A := pathSum σ.1 w) (c := -1) (pathUnit_cfg hr σ hw)
    (by
      rcases hsep with h | h
      · exact Or.inl h
      · right; rw [abs_neg, abs_one, mul_one, abs_of_nonneg (pathSum_nonneg _ _)]; exact h),
    abs_neg, abs_one, mul_one]

/-! ## The two configurations -/

/-- Test values: the position of each label in the path `τ`, divided by `N - 1`. -/
noncomputable def testW (τ : Equiv.Perm (Fin (r + 1 + 1))) : Point (r + 1 + 1) :=
  fun i => ((τ.symm i : ℕ) : ℝ) / ((r : ℝ) + 1)

/-- Reference values: `x_b = 1`, every middle coordinate `2`. -/
noncomputable def refW (r : ℕ) : Point (r + 1 + 1) :=
  fun i => if i = Fin.last (r + 1) then 1 else 2

theorem val_le_of_ne_last {a : Fin (r + 1 + 1)} (ha : a ≠ Fin.last (r + 1)) : (a : ℕ) ≤ r := by
  by_contra h
  apply ha
  apply Fin.ext
  rw [Fin.val_last]
  exact le_antisymm (Nat.lt_succ_iff.mp a.isLt) (Nat.succ_le_of_lt (not_le.mp h))

theorem testW_last (τ : PathIdx r) : testW τ.1 (Fin.last (r + 1)) = 1 := by
  unfold testW
  rw [τ.symm_last, Fin.val_last]
  push_cast
  exact div_self (by positivity)

theorem testW_middle (τ : PathIdx r) {i : Fin (r + 1 + 1)} (hi : i ≠ Fin.last (r + 1)) :
    testW τ.1 i + 2 * step r ≤ 1 := by
  unfold testW
  rw [two_step]
  have hk : ((τ.1.symm i : ℕ) : ℝ) ≤ r := by exact_mod_cast val_le_of_ne_last (τ.symm_ne_last hi)
  rw [div_add_div_same, div_le_one (by positivity)]
  linarith

theorem testW_separated (τ : PathIdx r) : Separated (testW τ.1) := by
  intro i _
  by_cases hi : i = Fin.last (r + 1)
  · left; rw [hi]; exact testW_last τ
  · right
    have h := testW_middle τ hi
    rw [abs_sub_comm, abs_of_nonneg (by linarith [step_pos r])]
    linarith

theorem refW_separated (r : ℕ) : Separated (refW r) := by
  intro i _
  unfold refW
  by_cases hi : i = Fin.last (r + 1)
  · left; rw [if_pos hi]
  · right
    rw [if_neg hi, two_step, show |(2 : ℝ) - 1| = 1 by norm_num]
    exact div_le_one_of_le (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) (by positivity)

theorem testW_eq_one_iff (τ : PathIdx r) (i : Fin (r + 1 + 1)) :
    testW τ.1 i = 1 ↔ refW r i = 1 := by
  unfold refW
  by_cases hi : i = Fin.last (r + 1)
  · rw [if_pos hi, hi, testW_last]
  · rw [if_neg hi]
    have h := testW_middle τ hi
    constructor
    · intro h1; linarith [step_pos r]
    · intro h1; norm_num at h1

/-! ## The separating functional -/

/-- `J` at the test configuration of `τ` minus `J` at the reference configuration. -/
noncomputable def pathFunctional (τ : Equiv.Perm (Fin (r + 1 + 1))) :
    (Point (r + 1 + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun g := jump (testW τ) g - jump (refW r) g
  map_add' f g := by simp only [jump, Pi.add_apply]; ring
  map_smul' c g := by simp only [jump, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem auxSpan_le_ker (τ : PathIdx r) :
    auxSpan (r + 1 + 1) ≤ LinearMap.ker (pathFunctional τ.1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply LinearMap.mem_ker.mpr
  change jump (testW τ.1) _ - jump (refW r) _ = 0
  rw [jump_feat_eq (testW_separated τ) (refW_separated r)
    (fun i _ => testW_eq_one_iff τ i) j, sub_self]

/-- A permutation fixing `0` which is not the identity has a descent at some
pair of consecutive positions `j + 1`, `j + 2`. -/
theorem exists_descent {g : Equiv.Perm (Fin (r + 1 + 1))} (h0 : g 0 = 0) (hg : g ≠ 1) :
    ∃ j : Fin r, g j.succ.succ < g j.castSucc.succ := by
  by_contra hno
  push_neg at hno
  apply hg
  have hmono : StrictMono g := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h1 : g (Fin.succ 0) ≠ 0 := fun h =>
        Fin.succ_ne_zero (0 : Fin (r + 1)) (g.injective (h.trans h0.symm))
      show g 0 < g (Fin.succ 0)
      rw [h0]
      exact lt_of_le_of_ne (Fin.zero_le _) (Ne.symm h1)
    · have hcs : (Fin.succ j).castSucc = j.castSucc.succ := Fin.ext rfl
      rw [hcs]
      refine lt_of_le_of_ne (hno j) fun he => ?_
      have := congrArg Fin.val (g.injective he)
      simp at this
  have hid : (g : Fin (r + 1 + 1) → Fin (r + 1 + 1)) = id :=
    Fin.strictMono_unique hmono strictMono_id (by rw [Set.range_id, Equiv.range_eq_univ])
  ext a
  exact congrArg Fin.val (congrFun hid a)

theorem pathSum_test (σ τ : PathIdx r) :
    (σ = τ → pathSum σ.1 (testW τ.1) = 0) ∧
      (σ ≠ τ → 2 * step r ≤ pathSum σ.1 (testW τ.1)) := by
  constructor
  · rintro rfl
    apply Finset.sum_eq_zero
    intro j _
    apply relu_of_nonpos
    unfold testW
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← sub_div]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    simp only [Fin.val_succ, Fin.coe_castSucc]
    push_cast
    linarith
  · intro hne
    let g : Equiv.Perm (Fin (r + 1 + 1)) := σ.1.trans τ.1.symm
    have hg0 : g 0 = 0 := by
      show τ.1.symm (σ.1 0) = 0
      rw [σ.map_zero, Equiv.symm_apply_eq, τ.map_zero]
    have hg1 : g ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      apply Equiv.ext
      intro a
      have h2 : g a = a := by rw [h]; rfl
      change τ.1.symm (σ.1 a) = a at h2
      rw [Equiv.symm_apply_eq] at h2
      exact h2
    obtain ⟨j, hj⟩ := exists_descent hg0 hg1
    have hterm : 2 * step r ≤ relu (testW τ.1 (σ.1 j.castSucc.succ) -
        testW τ.1 (σ.1 j.succ.succ)) := by
      unfold testW
      rw [← sub_div, two_step]
      have hlt : ((g j.succ.succ : ℕ) : ℝ) + 1 ≤ ((g j.castSucc.succ : ℕ) : ℝ) := by
        exact_mod_cast (show (g j.succ.succ : ℕ) + 1 ≤ g j.castSucc.succ from hj)
      refine le_trans ?_ (le_max_right _ _)
      apply div_le_div_of_le (by positivity)
      change (1 : ℝ) ≤ ((g j.castSucc.succ : ℕ) : ℝ) - ((g j.succ.succ : ℕ) : ℝ)
      linarith
    exact hterm.trans (Finset.single_le_sum (f := fun j : Fin r =>
      relu (testW τ.1 (σ.1 j.castSucc.succ) - testW τ.1 (σ.1 j.succ.succ)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ j))

theorem pathSum_ref (hr : 1 ≤ r) (σ : PathIdx r) : 1 ≤ pathSum σ.1 (refW r) := by
  let j₀ : Fin r := ⟨r - 1, by omega⟩
  have hlast : j₀.succ.succ = Fin.last (r + 1) := Fin.ext (by simp; omega)
  have hmid2 : j₀.castSucc.succ ≠ Fin.last (r + 1) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hterm : relu (refW r (σ.1 j₀.castSucc.succ) - refW r (σ.1 j₀.succ.succ)) = 1 := by
    unfold refW
    rw [hlast, σ.map_last, if_pos rfl, if_neg (σ.ne_last hmid2),
      show (2 : ℝ) - 1 = 1 by norm_num]
    exact relu_of_nonneg zero_le_one
  rw [← hterm]
  exact Finset.single_le_sum (f := fun j : Fin r =>
    relu (refW r (σ.1 j.castSucc.succ) - refW r (σ.1 j.succ.succ)))
    (fun _ _ => le_max_left _ _) (Finset.mem_univ j₀)

theorem pathFunctional_pathUnit (hr : 1 ≤ r) (σ τ : PathIdx r) :
    pathFunctional τ.1 (pathUnit hr σ.1) = if σ = τ then step r else 0 := by
  change jump (testW τ.1) _ - jump (refW r) _ = _
  have hT := pathSum_test σ τ
  have hR := pathSum_ref hr σ
  rw [jump_pathUnit hr σ (testW_last τ) (by
      by_cases h : σ = τ
      · exact Or.inl (hT.1 h)
      · exact Or.inr (by linarith [hT.2 h, step_pos r])),
    jump_pathUnit hr σ (by unfold refW; rw [if_pos rfl])
      (Or.inr (by linarith [step_le_one r])),
    if_neg (by linarith [step_le_one r] : pathSum σ.1 (refW r) ≠ 0), sub_zero]
  by_cases h : σ = τ
  · rw [if_pos (hT.1 h), if_pos h]
  · rw [if_neg (by linarith [hT.2 h, step_pos r] : pathSum σ.1 (testW τ.1) ≠ 0), if_neg h]

/-! ## The lower bound -/

/-- **Vocabulary-dimension lower bound.** For `N = r + 2 ≥ 3`, the
`(N - 2)!` all-cut path units with apex `0` and endpoint `N - 1` are linearly
independent modulo the auxiliary span; hence `q_N ≥ (N - 2)!`. -/
theorem factorial_le_quotientDim (r : ℕ) (hr : 1 ≤ r) : r.factorial ≤ quotientDim r := by
  let Aq := (auxSpan (r + 1 + 1)).comap (vocabularySpan r).subtype
  let v : PathIdx r → vocabularySpan r := fun σ => ⟨pathUnit hr σ.1, pathUnit_mem hr σ.1⟩
  have hli : LinearIndependent ℝ (fun σ => Aq.mkQ (v σ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc τ
    have h0 : Aq.mkQ (∑ σ, c σ • v σ) = 0 := by
      rw [map_sum]
      simpa only [map_smul] using hc
    have hmem : (∑ σ, c σ • pathUnit hr σ.1) ∈ auxSpan (r + 1 + 1) := by
      have h1 := (Submodule.Quotient.mk_eq_zero Aq).mp h0
      rw [Submodule.mem_comap] at h1
      change ((∑ σ, c σ • v σ : vocabularySpan r) : Point (r + 1 + 1) → ℝ) ∈ _ at h1
      rw [Submodule.coe_sum] at h1
      simpa only [Submodule.coe_smul] using h1
    have hL := LinearMap.mem_ker.mp (auxSpan_le_ker τ hmem)
    rw [map_sum] at hL
    simp only [map_smul, smul_eq_mul, pathFunctional_pathUnit hr] at hL
    rw [Finset.sum_eq_single τ (fun σ _ hσ => by rw [if_neg hσ, mul_zero])
      (fun h => absurd (Finset.mem_univ τ) h), if_pos rfl] at hL
    exact (mul_eq_zero.mp hL).resolve_right (step_pos r).ne'
  have h := FiniteDimensional.fintype_card_le_finrank_of_linearIndependent hli
  rwa [card_pathIdx] at h

end MaxCaterpillar
