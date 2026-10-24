import MaxCaterpillar.Quotient

/-! # The dimension bound `q_N ≥ (N - 2)!` by a third mixed difference

For every order `ρ` of the middle labels `1, …, N - 2` take the path unit
`U_ρ(x) = σ(x_b - x_0 + Σ_j σ(x_{ρ(j)} - x_{ρ(j+1)}))` with apex `0` and last
spine label `b = N - 1`. Let `c = ρ(N - 2)` and let `Λ_ρ` be the third mixed
forward difference, with step `1`, in the coordinates `x_0, x_b, x_c` at the
point `z` with `z_0 = z_b = z_c = 2r` and `z_{ρ(k)} = 2k`.

* `Λ_ρ` vanishes on every function of at most two coordinates, in particular
  on every auxiliary function: one of the three directions is not used.
* On the corners, `U_ρ = σ(x_b - x_0 + σ(x_c - x_b))`, and `Λ_ρ U_ρ = 1`.
* If `π ≠ ρ`, the path `π` has a descent in `z`, so the outer argument of `U_π`
  is nonnegative on the corners; there `U_π` is a sum of functions of at most
  two coordinates, and `Λ_ρ U_π = 0`.
-/

open BigOperators

namespace MaxCaterpillar.Dimension

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width ParamidGeom ParamidChain

variable {r : ℕ}

local notation "P" r => Point (r + 1 + 1)

/-! ## Mixed differences -/

/-- Raise coordinate `a` by `1`. -/
def shift (a : Fin (r + 1 + 1)) (x : P r) : P r := Function.update x a (x a + 1)

/-- Forward difference in direction `e_a`. -/
def D (a : Fin (r + 1 + 1)) (g : (P r) → ℝ) : (P r) → ℝ := fun x => g (shift a x) - g x

theorem shift_comm {a e : Fin (r + 1 + 1)} (h : a ≠ e) (x : P r) :
    shift a (shift e x) = shift e (shift a x) := by
  unfold shift
  rw [Function.update_noteq h, Function.update_noteq h.symm, Function.update_comm h]

/-- `g` does not depend on coordinate `a`. -/
def Indep (a : Fin (r + 1 + 1)) (g : (P r) → ℝ) : Prop := ∀ x, g (shift a x) = g x

theorem indep_D {a e : Fin (r + 1 + 1)} {g : (P r) → ℝ} (h : Indep a g) (hae : a ≠ e) :
    Indep a (D e g) := fun x => by unfold D; rw [← shift_comm hae, h, h]

theorem D_eq_zero {a : Fin (r + 1 + 1)} {g : (P r) → ℝ} (h : Indep a g) : D a g = 0 :=
  funext fun x => by unfold D; rw [h, sub_self]; rfl

theorem D_zero (a : Fin (r + 1 + 1)) : D a (0 : (P r) → ℝ) = 0 := funext fun _ => sub_self 0

/-- `Λ g = (D_a D_b D_c g)(z)`. -/
def Λ (a b c : Fin (r + 1 + 1)) (z : P r) : ((P r) → ℝ) →ₗ[ℝ] ℝ where
  toFun g := D a (D b (D c g)) z
  map_add' f g := by simp only [D, Pi.add_apply]; ring
  map_smul' t g := by simp only [D, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Λ_indep {a b c : Fin (r + 1 + 1)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (z : P r) {g : (P r) → ℝ} {e : Fin (r + 1 + 1)} (he : e = a ∨ e = b ∨ e = c)
    (hg : Indep e g) : Λ a b c z g = 0 := by
  show D a (D b (D c g)) z = 0
  rcases he with rfl | rfl | rfl
  · rw [D_eq_zero (indep_D (indep_D hg hac) hab)]; rfl
  · rw [D_eq_zero (indep_D hg hbc), D_zero]; rfl
  · rw [D_eq_zero hg, D_zero, D_zero]; rfl

/-- `Λ` kills every function of at most two coordinates. -/
theorem Λ_two {a b c : Fin (r + 1 + 1)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (z : P r) (φ : ℝ → ℝ → ℝ) (p q : Fin (r + 1 + 1)) :
    Λ a b c z (fun x => φ (x p) (x q)) = 0 := by
  have hI : ∀ e, e ≠ p → e ≠ q → Indep e (fun x : P r => φ (x p) (x q)) := fun e hp hq x => by
    simp only [shift, Function.update_noteq hp.symm, Function.update_noteq hq.symm]
  by_cases ha : a ≠ p ∧ a ≠ q
  · exact Λ_indep hab hac hbc z (Or.inl rfl) (hI a ha.1 ha.2)
  by_cases hb : b ≠ p ∧ b ≠ q
  · exact Λ_indep hab hac hbc z (Or.inr (Or.inl rfl)) (hI b hb.1 hb.2)
  refine Λ_indep hab hac hbc z (Or.inr (Or.inr rfl)) (hI c ?_ ?_) <;> intro h <;> subst h <;>
    push_neg at ha hb <;> by_cases h1 : a = c <;> simp_all

/-- Every auxiliary function is a function of at most two coordinates. -/
theorem feat_two {N : ℕ} (j : Fin (W N)) :
    ∃ (φ : ℝ → ℝ → ℝ) (p q : Fin N), ∀ x, feat N x j = φ (x p) (x q) :=
  Fin.addCases (motive := fun j : Fin (N + (N + N.choose 2)) =>
      ∃ (φ : ℝ → ℝ → ℝ) (p q : Fin N), ∀ x, feat N x j = φ (x p) (x q))
    (fun i => ⟨fun u _ => relu u, i, i, fun x => feat_pos x i⟩)
    (fun j => Fin.addCases (motive := fun j : Fin (N + N.choose 2) =>
        ∃ (φ : ℝ → ℝ → ℝ) (p q : Fin N), ∀ x, feat N x (Fin.natAdd N j) = φ (x p) (x q))
      (fun i => ⟨fun u _ => relu (-u), i, i, fun x => feat_neg x i⟩)
      (fun q => ⟨fun u v => relu (u - v), prFst q, prSnd q, fun x => feat_pr x q⟩) j) j

theorem auxSpan_le_ker {a b c : Fin (r + 1 + 1)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (z : P r) : auxSpan (r + 1 + 1) ≤ LinearMap.ker (Λ a b c z) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  obtain ⟨φ, p, q, h⟩ := feat_two j
  show Λ a b c z (fun x => feat (r + 1 + 1) x j) = 0
  rw [show (fun x => feat (r + 1 + 1) x j) = fun x => φ (x p) (x q) from funext h]
  exact Λ_two hab hac hbc z φ p q

/-- `Λ` only sees the box `z ≤ x ≤ z + 1`. -/
def InBox (z x : P r) : Prop := ∀ i, z i ≤ x i ∧ x i ≤ z i + 1

theorem InBox.shift {z x : P r} (hx : InBox z x) {e : Fin (r + 1 + 1)} (he : x e = z e) :
    InBox z (shift e x) := fun i => by
  unfold MaxCaterpillar.Dimension.shift
  by_cases hi : i = e
  · subst hi; rw [Function.update_same, he]; constructor <;> linarith
  · rw [Function.update_noteq hi]; exact hx i

theorem shift_ne {e i : Fin (r + 1 + 1)} (h : i ≠ e) (x : P r) : shift e x i = x i :=
  Function.update_noteq h _ _

theorem Λ_congr {a b c : Fin (r + 1 + 1)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {z : P r} {g h : (P r) → ℝ} (H : ∀ x, InBox z x → g x = h x) :
    Λ a b c z g = Λ a b c z h := by
  have hz : InBox z z := fun i => ⟨le_rfl, by linarith⟩
  have h3 : ∀ x, InBox z x → x c = z c → D c g x = D c h x := fun x hx hc => by
    show g (shift c x) - g x = h (shift c x) - h x
    rw [H x hx, H _ (hx.shift hc)]
  have h2 : ∀ x, InBox z x → x c = z c → x b = z b → D b (D c g) x = D b (D c h) x :=
    fun x hx hc hb => by
      show D c g (shift b x) - D c g x = D c h (shift b x) - D c h x
      rw [h3 x hx hc, h3 _ (hx.shift hb) (by rw [shift_ne hbc.symm, hc])]
  show D b (D c g) (shift a z) - D b (D c g) z = D b (D c h) (shift a z) - D b (D c h) z
  rw [h2 z hz rfl rfl, h2 _ (hz.shift rfl) (shift_ne hac.symm z) (shift_ne hab.symm z)]

/-- The germ of the matching unit: `Λ σ(x_b - x_a + σ(x_c - x_b)) = 1`. -/
theorem Λ_germ {a b c : Fin (r + 1 + 1)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {z : P r} (hb : z b = z a) (hc : z c = z a) :
    Λ a b c z (fun x => relu (x b - x a + relu (x c - x b))) = 1 := by
  show D a (D b (D c _)) z = 1
  simp only [D, shift, Function.update_apply, if_pos rfl, hab, hac, hbc, hab.symm, hac.symm,
    hbc.symm, if_false, hb, hc]
  norm_num [relu]

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

theorem PathIdx.middle (π : PathIdx r) {a : Fin (r + 1 + 1)} (ha : Middle r a) :
    Middle r (π.1 a) :=
  ⟨fun h => ha.1 (π.1.injective (h.trans π.map_zero.symm)),
    fun h => ha.2 (π.1.injective (h.trans π.map_last.symm))⟩

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
noncomputable def pathUnit (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r + 1 + 1))) : (P r) → ℝ :=
  realUnitY (wordKey (pathWord hr π))

theorem pathUnit_apply (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r + 1 + 1))) (x : P r) :
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

/-! ## The detectors -/

/-- The test point of `ρ`: `z_0 = z_b = 2r` and `z_{ρ(k)} = 2k` for middle `k`. -/
noncomputable def testZ (ρ : Equiv.Perm (Fin (r + 1 + 1))) : P r :=
  fun i => if Middle r i then 2 * ((ρ.symm i : ℕ) : ℝ) else 2 * r

theorem testZ_apply (ρ : PathIdx r) {k : Fin (r + 1 + 1)} (hk : Middle r k) :
    testZ ρ.1 (ρ.1 k) = 2 * (k : ℕ) := by
  unfold testZ; rw [if_pos (ρ.middle hk), Equiv.symm_apply_apply]

/-- Position `r`, the last middle position. -/
def cPos (r : ℕ) : Fin (r + 1 + 1) := ⟨r, by omega⟩

theorem middle_of_val {k : Fin (r + 1 + 1)} (h1 : 1 ≤ (k : ℕ)) (h2 : (k : ℕ) ≤ r) :
    Middle r k :=
  ⟨fun h => by rw [h] at h1; simp at h1, fun h => by rw [h, Fin.val_last] at h2; omega⟩

theorem last_ne_zero' : Fin.last (r + 1) ≠ (0 : Fin (r + 1 + 1)) := by
  intro h; have := congrArg Fin.val h; simp at this

/-- `Λ_ρ`: third mixed difference in `x_0, x_b, x_c`, `c = ρ(r)`, at `testZ ρ`. -/
noncomputable def detector (ρ : PathIdx r) : ((P r) → ℝ) →ₗ[ℝ] ℝ :=
  Λ 0 (Fin.last (r + 1)) (ρ.1 (cPos r)) (testZ ρ.1)

theorem detector_ne (hr : 1 ≤ r) (ρ : PathIdx r) :
    (0 : Fin (r + 1 + 1)) ≠ Fin.last (r + 1) ∧ (0 : Fin (r + 1 + 1)) ≠ ρ.1 (cPos r) ∧
      Fin.last (r + 1) ≠ ρ.1 (cPos r) := by
  have hc := ρ.middle (middle_of_val (k := cPos r) hr le_rfl)
  exact ⟨last_ne_zero'.symm, Ne.symm hc.1, Ne.symm hc.2⟩

theorem detector_aux (hr : 1 ≤ r) (ρ : PathIdx r) :
    auxSpan (r + 1 + 1) ≤ LinearMap.ker (detector ρ) :=
  let h := detector_ne hr ρ
  auxSpan_le_ker h.1 h.2.1 h.2.2 _

theorem testZ_zero (ρ : PathIdx r) : testZ ρ.1 0 = 2 * r := if_neg fun h => h.1 rfl

theorem testZ_last (ρ : PathIdx r) : testZ ρ.1 (Fin.last (r + 1)) = 2 * r :=
  if_neg fun h => h.2 rfl

theorem detector_self (hr : 1 ≤ r) (ρ : PathIdx r) : detector ρ (pathUnit hr ρ.1) = 1 := by
  obtain ⟨h0l, h0c, hlc⟩ := detector_ne hr ρ
  have hcm : Middle r (cPos r) := middle_of_val hr le_rfl
  unfold detector
  rw [Λ_congr h0l h0c hlc (h := fun x => relu (x (Fin.last (r + 1)) - x 0 +
      relu (x (ρ.1 (cPos r)) - x (Fin.last (r + 1))))),
    Λ_germ h0l h0c hlc (by rw [testZ_last, testZ_zero])
      (by rw [testZ_apply ρ hcm, testZ_zero]; rfl)]
  intro x hx
  rw [pathUnit_apply, ρ.map_last, ρ.map_zero]
  congr 2
  let j₀ : Fin r := ⟨r - 1, by omega⟩
  rw [Finset.sum_eq_single j₀]
  · congr 2
    · rw [show j₀.castSucc.succ = cPos r from Fin.ext (show r - 1 + 1 = r by omega)]
    · rw [show j₀.succ.succ = Fin.last (r + 1) from Fin.ext (show r - 1 + 1 + 1 = r + 1 by omega),
        ρ.map_last]
  · intro j _ hj
    have hjr : (j : ℕ) + 2 ≤ r := by
      rcases Nat.lt_or_ge ((j : ℕ) + 1) r with h | h
      · omega
      · have hj' : (j : ℕ) = r - 1 :=
          Nat.le_antisymm (Nat.le_sub_of_add_le j.isLt) (Nat.sub_le_of_le_add h)
        exact absurd (Fin.ext hj' : j = j₀) hj
    have h1 := (hx (ρ.1 j.castSucc.succ)).2
    have h2 := (hx (ρ.1 j.succ.succ)).1
    rw [testZ_apply ρ (middle_of_val (by simp) (by simp; omega))] at h1
    rw [testZ_apply ρ (middle_of_val (by simp) (by simp; omega))] at h2
    simp only [Fin.val_succ, Fin.coe_castSucc] at h1 h2
    push_cast at h1 h2
    exact relu_of_nonpos (by linarith)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem detector_other (hr : 1 ≤ r) {π ρ : PathIdx r} (hne : π ≠ ρ) :
    detector ρ (pathUnit hr π.1) = 0 := by
  obtain ⟨h0l, h0c, hlc⟩ := detector_ne hr ρ
  let hinge : Fin r → (P r) → ℝ := fun j x =>
    relu (x (π.1 j.castSucc.succ) - x (π.1 j.succ.succ))
  have hlin : detector ρ ((fun x => (fun u v => u - v) (x (Fin.last (r + 1))) (x 0)) +
      ∑ j, hinge j) = 0 := by
    unfold detector
    rw [map_add, map_sum, Λ_two h0l h0c hlc, zero_add]
    exact Finset.sum_eq_zero fun j _ => Λ_two h0l h0c hlc _ (fun u v => relu (u - v)) _ _
  rw [← hlin]
  unfold detector
  apply Λ_congr h0l h0c hlc
  intro x hx
  -- a descent of `ρ⁻¹ π` gives a hinge at least `1` on the box
  let g : Equiv.Perm (Fin (r + 1 + 1)) := π.1.trans ρ.1.symm
  have hg0 : g 0 = 0 := by
    show ρ.1.symm (π.1 0) = 0; rw [π.map_zero, Equiv.symm_apply_eq, ρ.map_zero]
  have hg1 : g ≠ 1 := fun h => hne (Subtype.ext (Equiv.ext fun a => by
    have h2 : g a = a := by rw [h]; rfl
    exact (Equiv.symm_apply_eq _).mp h2))
  obtain ⟨j, hj⟩ := exists_descent hg0 hg1
  have hm1 : Middle r (g j.castSucc.succ) := by
    refine (PathIdx.middle ⟨ρ.1.symm, fun a ha => ?_⟩ (π.middle (middle_of_val
      (by simp) (by simp; exact j.isLt))))
    rw [Equiv.symm_apply_eq, ρ.2 a ha]
  have hz : ∀ k, π.1 k = ρ.1 (g k) := fun k => by
    show π.1 k = ρ.1 (ρ.1.symm (π.1 k)); rw [Equiv.apply_symm_apply]
  clear_value g
  have hm2 : Middle r (g j.succ.succ) := by
    refine middle_of_val ?_ ?_
    · rcases Nat.eq_zero_or_pos (g j.succ.succ : ℕ) with h | h
      · exfalso
        have : g j.succ.succ = 0 := Fin.ext h
        exact Fin.succ_ne_zero _ (g.injective (this.trans hg0.symm))
      · exact h
    · have := hm1.2; have hlt : (g j.succ.succ : ℕ) < g j.castSucc.succ := hj
      have hle : (g j.castSucc.succ : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp (g j.castSucc.succ).isLt
      have hne : (g j.castSucc.succ : ℕ) ≠ r + 1 := fun h => this (Fin.ext (h.trans (Fin.val_last _).symm))
      exact Nat.le_of_lt_succ (lt_trans hlt (lt_of_le_of_ne hle hne))
  have h1 := (hx (π.1 j.castSucc.succ)).1
  have h2 := (hx (π.1 j.succ.succ)).2
  rw [hz, testZ_apply ρ hm1] at h1
  rw [hz, testZ_apply ρ hm2] at h2
  have hgap : ((g j.succ.succ : ℕ) : ℝ) + 1 ≤ (g j.castSucc.succ : ℕ) := by
    exact_mod_cast (show (g j.succ.succ : ℕ) + 1 ≤ g j.castSucc.succ from hj)
  have hterm : 1 ≤ hinge j x := by
    refine le_trans ?_ (le_max_right _ _)
    rw [hz, hz]; linarith
  have hsum : hinge j x ≤ ∑ j, hinge j x :=
    Finset.single_le_sum (f := fun j => hinge j x) (fun _ _ => le_max_left _ _)
      (Finset.mem_univ j)
  have hb := (hx (Fin.last (r + 1))).1
  have h0 := (hx 0).2
  rw [testZ_last] at hb
  rw [testZ_zero] at h0
  have hsum' : 1 ≤ ∑ j : Fin r, relu (x (π.1 j.castSucc.succ) - x (π.1 j.succ.succ)) :=
    le_trans hterm hsum
  rw [pathUnit_apply, π.map_last, π.map_zero]
  show max 0 _ = _
  rw [max_eq_right (by linarith)]
  simp only [Pi.add_apply, Finset.sum_apply]

/-! ## The bound -/

/-- **Dimension of the caterpillar span.** For `N = r + 2 ≥ 3`, the `(N - 2)!`
path units with apex `0` and endpoint `N - 1` are linearly independent modulo
the auxiliary span; hence `q_N ≥ (N - 2)!`. -/
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
      change ((∑ σ, c σ • v σ : vocabularySpan r) : (P r) → ℝ) ∈ _ at h1
      rw [Submodule.coe_sum] at h1
      simpa only [Submodule.coe_smul] using h1
    have hL := LinearMap.mem_ker.mp (detector_aux hr τ hmem)
    rw [map_sum, Finset.sum_eq_single τ (fun σ _ hσ => by rw [map_smul, detector_other hr hσ,
      smul_zero]) (fun h => absurd (Finset.mem_univ τ) h), map_smul, detector_self, smul_eq_mul,
      mul_one] at hL
    exact hL
  have h := FiniteDimensional.fintype_card_le_finrank_of_linearIndependent hli
  rwa [card_pathIdx] at h

end MaxCaterpillar.Dimension
