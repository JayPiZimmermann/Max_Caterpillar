import MaxNN.Constructions.Paramid.Geom.Defs
import MaxNN.PolyhedralGeometry.SupportCut.Dot
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Determinants and orientation signs of lists of vectors

Helper of `Geom/Boundary.lean` (module `M-Boundary` of
`work/depth2_simplex/lean_core/BLUEPRINT.md`).  The realization of a chain relative to a frame
`[u₁, …, u_r]` carries the sign of `det [u₁, …, u_r, v₁, …, v_k, γ]`.  Here this determinant is
the determinant `ldet l` of a list `l` of vectors of `ℝ^N` (the entries of `l` are the rows; the
determinant of the transpose is the same), and `lsign l` is its sign (`0` unless `l` has exactly
`N` entries).

* `sgn x ∈ {−1, 0, 1}`, the sign of a real number with the casts used by `orient`.
* Row operations: linearity in one entry (`ldet_append_cons_add`, `ldet_append_cons_smul`),
  adjacent swaps (`ldet_swap`), moving an entry to the front of a block (`ldet_move`,
  sign `(−1)^{|B|}`), adding one entry to the last one (`ldet_append_add_row`).
* **Exchange** (`ldet_exchange`): if a functional `ℓ` kills every entry except the one in
  position `|A|`, then `⟨ℓ, u⟩ · det (A, x, B) = ⟨ℓ, x⟩ · det (A, u, B)`.
* **Projection functional** (`exists_proj_of_linearIndependent`): if `A ++ x :: B` is linearly
  independent, there is `ℓ` killing `A`, agreeing with `⟨x, ·⟩` on `A^⊥`, with `⟨ℓ, x⟩ > 0`
  (`ℓ` is the component of `x` orthogonal to `span A`, obtained from the Gram matrix of `A`).
  With the exchange this yields `lsign (A ++ y :: B) = sgn ⟨x, y⟩ · lsign (A ++ x :: B)` whenever
  `y` and `B` lie in `A^⊥` and `B ⊥ x` (`lsign_exchange_of_perp`).

Everything here is generic and lives in the sub-namespace `MaxNN.ParamidGeom.BoundaryAux`, so that
it cannot collide with helpers of sibling modules.
-/

namespace MaxNN.ParamidGeom

namespace BoundaryAux

open BigOperators

noncomputable section

variable {N : ℕ}

/-! ## The real sign -/

/-- The sign `−1, 0, 1` of a real number, with the casts used by `orient`. -/
def sgn (x : ℝ) : ℝ := ((SignType.sign x : ℤ) : ℝ)

theorem sgn_of_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := by
  simp [sgn, sign_pos h]

theorem sgn_of_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  simp [sgn, sign_neg h]

theorem sgn_zero : sgn 0 = 0 := by
  simp [sgn]

theorem sgn_mul (a b : ℝ) : sgn (a * b) = sgn a * sgn b := by
  rcases lt_trichotomy a 0 with ha | ha | ha <;> rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [sgn_of_pos (mul_pos_of_neg_of_neg ha hb), sgn_of_neg ha, sgn_of_neg hb]; norm_num
  · rw [hb, mul_zero, sgn_zero, mul_zero]
  · rw [sgn_of_neg (mul_neg_of_neg_of_pos ha hb), sgn_of_neg ha, sgn_of_pos hb]; norm_num
  · rw [ha, zero_mul, sgn_zero, zero_mul]
  · rw [ha, zero_mul, sgn_zero, zero_mul]
  · rw [ha, zero_mul, sgn_zero, zero_mul]
  · rw [sgn_of_neg (mul_neg_of_pos_of_neg ha hb), sgn_of_pos ha, sgn_of_neg hb]; norm_num
  · rw [hb, mul_zero, sgn_zero, mul_zero]
  · rw [sgn_of_pos (mul_pos ha hb), sgn_of_pos ha, sgn_of_pos hb]; norm_num

theorem sgn_neg (a : ℝ) : sgn (-a) = -sgn a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [sgn_of_pos (neg_pos.mpr ha), sgn_of_neg ha]; norm_num
  · rw [ha, neg_zero, sgn_zero, neg_zero]
  · rw [sgn_of_neg (neg_lt_zero.mpr ha), sgn_of_pos ha]

theorem sgn_mul_self {a : ℝ} (h : a ≠ 0) : sgn a * sgn a = 1 := by
  rcases lt_or_gt_of_ne h with ha | ha
  · rw [sgn_of_neg ha]; norm_num
  · rw [sgn_of_pos ha]; norm_num

theorem sgn_mul_abs (a : ℝ) : sgn a * |a| = a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [sgn_of_neg ha, abs_of_neg ha]; ring
  · rw [ha, sgn_zero, zero_mul]
  · rw [sgn_of_pos ha, abs_of_pos ha, one_mul]

theorem sgn_pos_mul {c : ℝ} (hc : 0 < c) (a : ℝ) : sgn (c * a) = sgn a := by
  rw [sgn_mul, sgn_of_pos hc, one_mul]

theorem sgn_neg_one_pow_mul (n : ℕ) (a : ℝ) : sgn ((-1) ^ n * a) = (-1) ^ n * sgn a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (-1 : ℝ) ^ (n + 1) * a = -((-1) ^ n * a) := by ring
    rw [e, sgn_neg, ih, pow_succ]
    ring

/-! ## Determinants of lists of vectors -/

/-- The `N × N` matrix whose `i`-th row is the `i`-th entry of `l` (zero rows past its end). -/
def lmat (l : List (Fin N → ℝ)) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i => l.getD i 0

/-- The determinant of the entries of `l` (as rows, equivalently as columns). -/
def ldet (l : List (Fin N → ℝ)) : ℝ := (lmat l).det

/-- The orientation sign of the `N` entries of `l` (`0` unless `l` has exactly `N` entries). -/
def lsign (l : List (Fin N → ℝ)) : ℝ := if l.length = N then sgn (ldet l) else 0

theorem lsign_of_length_ne {l : List (Fin N → ℝ)} (h : l.length ≠ N) : lsign l = 0 := by
  unfold lsign
  rw [if_neg h]

theorem lsign_of_length_eq {l : List (Fin N → ℝ)} (h : l.length = N) : lsign l = sgn (ldet l) := by
  unfold lsign
  rw [if_pos h]

/-! ### Entries of concatenations -/

theorem getD_mem_or_eq {α : Type*} (l : List α) (n : ℕ) (d : α) :
    l.getD n d ∈ l ∨ l.getD n d = d := by
  rcases lt_or_le n l.length with h | h
  · left
    rw [List.getD_eq_get _ _ h]
    exact List.get_mem _ _ _
  · right
    exact List.getD_eq_default _ _ h

theorem getD_append_cons_self {α : Type*} (A B : List α) (x d : α) :
    (A ++ x :: B).getD A.length d = x := by
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

theorem getD_append_cons_of_ne {α : Type*} (A B : List α) (x y d : α) {n : ℕ}
    (hn : n ≠ A.length) : (A ++ x :: B).getD n d = (A ++ y :: B).getD n d := by
  rcases lt_or_gt_of_ne hn with h | h
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h.le, List.getD_append_right _ _ _ _ h.le]
    obtain ⟨m, hm⟩ : ∃ m, n - A.length = m + 1 := ⟨n - A.length - 1, by omega⟩
    rw [hm, List.getD_cons_succ, List.getD_cons_succ]

theorem append_cons_cons_eq {α : Type*} (A B : List α) (a b : α) :
    A ++ a :: b :: B = (A ++ [a]) ++ b :: B := by
  simp

/-- Replacing one entry of the list is a row update of the matrix. -/
theorem lmat_append_cons (A B : List (Fin N → ℝ)) (x y : Fin N → ℝ) (hA : A.length < N) :
    lmat (A ++ x :: B) = Matrix.updateRow (lmat (A ++ y :: B)) ⟨A.length, hA⟩ x := by
  ext i j
  rw [Matrix.updateRow_apply]
  split_ifs with h
  · subst h
    show (A ++ x :: B).getD A.length 0 j = x j
    rw [getD_append_cons_self]
  · have hn : (i : ℕ) ≠ A.length := fun h' => h (Fin.ext h')
    show (A ++ x :: B).getD i 0 j = (A ++ y :: B).getD i 0 j
    rw [getD_append_cons_of_ne A B x y 0 hn]

/-! ### Row operations -/

theorem ldet_append_cons_add (A B : List (Fin N → ℝ)) (x y : Fin N → ℝ) (hA : A.length < N) :
    ldet (A ++ (x + y) :: B) = ldet (A ++ x :: B) + ldet (A ++ y :: B) := by
  unfold ldet
  rw [lmat_append_cons A B (x + y) 0 hA, lmat_append_cons A B x 0 hA,
    lmat_append_cons A B y 0 hA, Matrix.det_updateRow_add]

theorem ldet_append_cons_smul (A B : List (Fin N → ℝ)) (c : ℝ) (x : Fin N → ℝ)
    (hA : A.length < N) : ldet (A ++ (c • x) :: B) = c * ldet (A ++ x :: B) := by
  unfold ldet
  rw [lmat_append_cons A B (c • x) 0 hA, lmat_append_cons A B x 0 hA,
    Matrix.det_updateRow_smul]

/-- Two equal entries (among the first `N`) make the determinant vanish. -/
theorem ldet_eq_zero_of_getD_eq (l : List (Fin N → ℝ)) {i j : ℕ} (hi : i < N) (hj : j < N)
    (hij : i ≠ j) (h : l.getD i 0 = l.getD j 0) : ldet l = 0 :=
  Matrix.det_zero_of_row_eq (i := (⟨i, hi⟩ : Fin N)) (j := ⟨j, hj⟩)
    (fun e => hij (congrArg Fin.val e)) h

/-- **Adjacent swap.** -/
theorem ldet_swap (A B : List (Fin N → ℝ)) (x y : Fin N → ℝ) (hA : A.length + 1 < N) :
    ldet (A ++ x :: y :: B) = -ldet (A ++ y :: x :: B) := by
  have hA0 : A.length < N := by omega
  -- `det (…, a, b, …)` is linear in `a` and in `b`
  have lin1 : ∀ a b c : Fin N → ℝ,
      ldet (A ++ (a + b) :: c :: B) = ldet (A ++ a :: c :: B) + ldet (A ++ b :: c :: B) :=
    fun a b c => ldet_append_cons_add A (c :: B) a b hA0
  have lin2 : ∀ a b c : Fin N → ℝ,
      ldet (A ++ c :: (a + b) :: B) = ldet (A ++ c :: a :: B) + ldet (A ++ c :: b :: B) := by
    intro a b c
    have hc : (A ++ [c]).length < N := by
      rw [List.length_append, List.length_singleton]; exact hA
    rw [append_cons_cons_eq A B c (a + b), append_cons_cons_eq A B c a,
      append_cons_cons_eq A B c b]
    exact ldet_append_cons_add (A ++ [c]) B a b hc
  have rep : ∀ a : Fin N → ℝ, ldet (A ++ a :: a :: B) = 0 := by
    intro a
    refine ldet_eq_zero_of_getD_eq _ hA0 hA (by omega) ?_
    rw [getD_append_cons_self, append_cons_cons_eq A B a a]
    have e : A.length + 1 = (A ++ [a]).length := by
      rw [List.length_append, List.length_singleton]
    rw [e, getD_append_cons_self]
  have h0 := rep (x + y)
  rw [lin1, lin2, lin2, rep, rep] at h0
  linarith

/-- **Moving an entry to the front of a block** of `|B|` entries costs `(−1)^{|B|}`. -/
theorem ldet_move (A B C : List (Fin N → ℝ)) (x : Fin N → ℝ)
    (hlen : (A ++ B ++ x :: C).length ≤ N) :
    ldet (A ++ B ++ x :: C) = (-1) ^ B.length * ldet (A ++ x :: (B ++ C)) := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih =>
    have e1 : A ++ b :: B ++ x :: C = (A ++ [b]) ++ B ++ x :: C := by simp
    have hlen' : ((A ++ [b]) ++ B ++ x :: C).length ≤ N := by rw [← e1]; exact hlen
    rw [e1, ih (A ++ [b]) hlen']
    have e2 : (A ++ [b]) ++ x :: (B ++ C) = A ++ b :: x :: (B ++ C) := by simp
    have hA : A.length + 1 < N := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    rw [e2, ldet_swap A (B ++ C) b x hA, List.length_cons, List.cons_append, pow_succ]
    ring

/-- Adding the entry in position `|A|` to the last entry does not change the determinant. -/
theorem ldet_append_add_row (A B : List (Fin N → ℝ)) (x y : Fin N → ℝ)
    (hlen : (A ++ x :: B ++ [y]).length ≤ N) :
    ldet (A ++ x :: B ++ [y + x]) = ldet (A ++ x :: B ++ [y]) := by
  have hl : (A ++ x :: B).length < N := by
    simp only [List.length_append, List.length_cons, List.length_singleton] at hlen ⊢
    omega
  rw [ldet_append_cons_add (A ++ x :: B) [] y x hl]
  have h0 : ldet (A ++ x :: B ++ [x]) = 0 := by
    refine ldet_eq_zero_of_getD_eq _ (i := A.length) (j := (A ++ x :: B).length)
      (lt_of_le_of_lt (by simp) hl) hl (by simp) ?_
    rw [getD_append_cons_self, List.getD_append _ _ _ _ (by simp), getD_append_cons_self]
  rw [h0, add_zero]

/-- **Exchange.**  If `ℓ` kills every entry of `A` and of `B`, then
`⟨ℓ, u⟩ · det (A, x, B) = ⟨ℓ, x⟩ · det (A, u, B)`. -/
theorem ldet_exchange (A B : List (Fin N → ℝ)) (x u ℓ : Fin N → ℝ) (hA : A.length < N)
    (hℓA : ∀ a ∈ A, dot ℓ a = 0) (hℓB : ∀ b ∈ B, dot ℓ b = 0) :
    dot ℓ u * ldet (A ++ x :: B) = dot ℓ x * ldet (A ++ u :: B) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    simp [dot]
  have key : ldet (A ++ (dot ℓ u • x + (-dot ℓ x) • u) :: B) = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨ℓ, hℓ, ?_⟩
    funext i
    rw [Pi.zero_apply]
    show dot ((A ++ (dot ℓ u • x + (-dot ℓ x) • u) :: B).getD i 0) ℓ = 0
    rw [SupportCut.dot_comm]
    rcases getD_mem_or_eq (A ++ (dot ℓ u • x + (-dot ℓ x) • u) :: B) i 0 with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hℓA _ h
      · rcases List.mem_cons.mp h with h | h
        · rw [h, SupportCut.dot_add_right, SupportCut.dot_smul_right, SupportCut.dot_smul_right]
          ring
        · exact hℓB _ h
    · rw [h]
      simp [dot]
  rw [ldet_append_cons_add _ _ _ _ hA, ldet_append_cons_smul _ _ _ _ hA,
    ldet_append_cons_smul _ _ _ _ hA] at key
  linarith

/-! ### The projection functional -/

/-- Orthogonal projection onto the span of an independent family, via the Gram matrix:
there are coefficients `c` with `x − ∑ c_j f_j ⊥ f_i` for all `i`. -/
theorem exists_perp_coeffs {r : ℕ} (f : Fin r → (Fin N → ℝ)) (hf : LinearIndependent ℝ f)
    (x : Fin N → ℝ) : ∃ c : Fin r → ℝ, ∀ i, dot (x - ∑ j, c j • f j) (f i) = 0 := by
  classical
  let G : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => dot (f j) (f i)
  have hG : ∀ (c : Fin r → ℝ) (i : Fin r), G.mulVec c i = dot (∑ j, c j • f j) (f i) := by
    intro c i
    show ∑ j, dot (f j) (f i) * c j = _
    rw [SupportCut.dot_comm, SupportCut.dot_sum_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [SupportCut.dot_comm, mul_comm]
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hs : ∑ j, v j • f j = 0 := by
      apply SupportCut.eq_zero_of_dot_self_eq_zero
      rw [SupportCut.dot_sum_smul_right]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← hG v i, hGv, Pi.zero_apply, mul_zero]
    exact hv (funext fun j => Fintype.linearIndependent_iff.mp hf v hs j)
  refine ⟨G⁻¹.mulVec (fun i => dot x (f i)), fun i => ?_⟩
  rw [SupportCut.dot_sub_left, ← hG, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  exact sub_self _

/-- **Projection functional.**  If `A` is linearly independent and `x ∉ span A`, the component
`ℓ` of `x` orthogonal to `span A` kills `A`, agrees with `⟨x, ·⟩` on `A^⊥`, and `⟨ℓ, x⟩ > 0`. -/
theorem exists_proj_functional (A : List (Fin N → ℝ)) (x : Fin N → ℝ)
    (hA : LinearIndependent ℝ (fun i : Fin A.length => A.get i))
    (hx : x ∉ Submodule.span ℝ (Set.range (fun i : Fin A.length => A.get i))) :
    ∃ ℓ : Fin N → ℝ, (∀ a ∈ A, dot ℓ a = 0) ∧
      (∀ y, (∀ a ∈ A, dot a y = 0) → dot ℓ y = dot x y) ∧ 0 < dot ℓ x := by
  obtain ⟨c, hc⟩ := exists_perp_coeffs (fun i : Fin A.length => A.get i) hA x
  refine ⟨x - ∑ j, c j • A.get j, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact hc i
  · intro y hy
    rw [SupportCut.dot_sub_left, SupportCut.dot_comm (∑ j, c j • A.get j),
      SupportCut.dot_sum_smul_right]
    have h0 : ∑ j, c j * dot y (A.get j) = 0 := Finset.sum_eq_zero fun j _ => by
      rw [SupportCut.dot_comm, hy _ (List.get_mem _ _ _), mul_zero]
    rw [h0, sub_zero]
  · have hℓ0 : x - ∑ j, c j • A.get j ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero.mp h]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hxℓ : dot (x - ∑ j, c j • A.get j) x =
        dot (x - ∑ j, c j • A.get j) (x - ∑ j, c j • A.get j) := by
      have h0 : ∑ j, c j * dot (x - ∑ j, c j • A.get j) (A.get j) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hc j, mul_zero]
      calc dot (x - ∑ j, c j • A.get j) x =
            dot (x - ∑ j, c j • A.get j) ((x - ∑ j, c j • A.get j) + ∑ j, c j • A.get j) := by
              rw [sub_add_cancel]
        _ = dot (x - ∑ j, c j • A.get j) (x - ∑ j, c j • A.get j) +
              ∑ j, c j * dot (x - ∑ j, c j • A.get j) (A.get j) := by
              rw [SupportCut.dot_add_right, SupportCut.dot_sum_smul_right]
        _ = _ := by rw [h0, add_zero]
    rw [hxℓ]
    have hnn : 0 ≤ dot (x - ∑ j, c j • A.get j) (x - ∑ j, c j • A.get j) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (SupportCut.eq_zero_of_dot_self_eq_zero h.symm) hℓ0

theorem get_append_cons_self {α : Type*} (A B : List α) (x : α)
    (h : A.length < (A ++ x :: B).length) : (A ++ x :: B).get ⟨A.length, h⟩ = x := by
  rw [← List.getD_eq_get _ x h, getD_append_cons_self]

/-- **Projection functional from an independent list `A ++ x :: B`.** -/
theorem exists_proj_of_linearIndependent (A B : List (Fin N → ℝ)) (x : Fin N → ℝ)
    (h : LinearIndependent ℝ (fun i : Fin (A ++ x :: B).length => (A ++ x :: B).get i)) :
    ∃ ℓ : Fin N → ℝ, (∀ a ∈ A, dot ℓ a = 0) ∧
      (∀ y, (∀ a ∈ A, dot a y = 0) → dot ℓ y = dot x y) ∧ 0 < dot ℓ x := by
  have hlt : ∀ i : Fin A.length, (i : ℕ) < (A ++ x :: B).length := fun i => by
    rw [List.length_append]; exact lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
  let ι : Fin A.length → Fin (A ++ x :: B).length := fun i => ⟨i, hlt i⟩
  have hι : Function.Injective ι := fun i j hij => by
    have h' := congrArg Fin.val hij
    exact Fin.ext h'
  have hget : ∀ i : Fin A.length, (A ++ x :: B).get (ι i) = A.get i := fun i =>
    List.get_append _ i.2
  have hA : LinearIndependent ℝ (fun i : Fin A.length => A.get i) := by
    have h2 := h.comp ι hι
    have e : ((fun i : Fin (A ++ x :: B).length => (A ++ x :: B).get i) ∘ ι) =
        fun i : Fin A.length => A.get i := funext hget
    rwa [e] at h2
  have hx0 : A.length < (A ++ x :: B).length := by simp
  have hx : x ∉ Submodule.span ℝ (Set.range (fun i : Fin A.length => A.get i)) := by
    have hnot : (⟨A.length, hx0⟩ : Fin (A ++ x :: B).length) ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      simp only at this
      exact absurd i.2 (by omega)
    have h3 := h.not_mem_span_image hnot
    rw [get_append_cons_self] at h3
    intro hmem
    apply h3
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨i, rfl⟩
    exact ⟨ι i, ⟨i, rfl⟩, hget i⟩
  exact exists_proj_functional A x hA hx

/-! ### Signs -/

theorem lsign_swap (A B : List (Fin N → ℝ)) (x y : Fin N → ℝ) :
    lsign (A ++ x :: y :: B) = -lsign (A ++ y :: x :: B) := by
  by_cases hl : (A ++ x :: y :: B).length = N
  · have hl' : (A ++ y :: x :: B).length = N := by simpa using hl
    rw [lsign_of_length_eq hl, lsign_of_length_eq hl',
      ldet_swap A B x y (by simp at hl; omega), sgn_neg]
  · have hl' : (A ++ y :: x :: B).length ≠ N := by simpa using hl
    rw [lsign_of_length_ne hl, lsign_of_length_ne hl', neg_zero]

theorem lsign_move (A B C : List (Fin N → ℝ)) (x : Fin N → ℝ) :
    lsign (A ++ B ++ x :: C) = (-1) ^ B.length * lsign (A ++ x :: (B ++ C)) := by
  by_cases hl : (A ++ B ++ x :: C).length = N
  · have hl' : (A ++ x :: (B ++ C)).length = N := by
      simp only [List.length_append, List.length_cons] at hl ⊢; omega
    rw [lsign_of_length_eq hl, lsign_of_length_eq hl', ldet_move A B C x hl.le,
      sgn_neg_one_pow_mul]
  · have hl' : (A ++ x :: (B ++ C)).length ≠ N := by
      simp only [List.length_append, List.length_cons] at hl ⊢; omega
    rw [lsign_of_length_ne hl, lsign_of_length_ne hl', mul_zero]

theorem lsign_append_add_row (A B : List (Fin N → ℝ)) (x y : Fin N → ℝ) :
    lsign (A ++ x :: B ++ [y + x]) = lsign (A ++ x :: B ++ [y]) := by
  by_cases hl : (A ++ x :: B ++ [y]).length = N
  · have hl' : (A ++ x :: B ++ [y + x]).length = N := by simpa using hl
    rw [lsign_of_length_eq hl, lsign_of_length_eq hl', ldet_append_add_row A B x y hl.le]
  · have hl' : (A ++ x :: B ++ [y + x]).length ≠ N := by simpa using hl
    rw [lsign_of_length_ne hl, lsign_of_length_ne hl']

/-- **Exchange of signs.**  If `ℓ` kills `A` and `B` and `⟨ℓ, u⟩ > 0`, then
`lsign (A ++ x :: B) = sgn ⟨ℓ, x⟩ · lsign (A ++ u :: B)`. -/
theorem lsign_exchange (A B : List (Fin N → ℝ)) (x u ℓ : Fin N → ℝ)
    (hℓA : ∀ a ∈ A, dot ℓ a = 0) (hℓB : ∀ b ∈ B, dot ℓ b = 0) (hu : 0 < dot ℓ u) :
    lsign (A ++ x :: B) = sgn (dot ℓ x) * lsign (A ++ u :: B) := by
  by_cases hl : (A ++ x :: B).length = N
  · have hl' : (A ++ u :: B).length = N := by simpa using hl
    rw [lsign_of_length_eq hl, lsign_of_length_eq hl']
    have hA : A.length < N := by simp at hl; omega
    have h := congrArg sgn (ldet_exchange A B x u ℓ hA hℓA hℓB)
    rw [sgn_mul, sgn_mul, sgn_of_pos hu, one_mul] at h
    exact h
  · have hl' : (A ++ u :: B).length ≠ N := by simpa using hl
    rw [lsign_of_length_ne hl, lsign_of_length_ne hl', mul_zero]

/-- **Exchange against the frame.**  Let `A ++ u :: C` be linearly independent.  If `x` and every
entry of `B` are orthogonal to every entry of `A`, and every entry of `B` is orthogonal to `u`,
then `lsign (A ++ x :: B) = sgn ⟨u, x⟩ · lsign (A ++ u :: B)`. -/
theorem lsign_exchange_of_perp (A B C : List (Fin N → ℝ)) (x u : Fin N → ℝ)
    (hind : LinearIndependent ℝ (fun i : Fin (A ++ u :: C).length => (A ++ u :: C).get i))
    (hxA : ∀ a ∈ A, dot a x = 0) (hBA : ∀ b ∈ B, ∀ a ∈ A, dot a b = 0)
    (hBu : ∀ b ∈ B, dot u b = 0) :
    lsign (A ++ x :: B) = sgn (dot u x) * lsign (A ++ u :: B) := by
  obtain ⟨ℓ, hℓA, hℓ, hpos⟩ := exists_proj_of_linearIndependent A C u hind
  rw [lsign_exchange A B x u ℓ hℓA
      (fun b hb => by rw [hℓ b (fun a ha => hBA b hb a ha)]; exact hBu b hb) hpos, hℓ x hxA]

end

end BoundaryAux

end MaxNN.ParamidGeom
