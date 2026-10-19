import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.Module.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The root lattice `Γ_n`, the positive roots `t_{ab}`, and face relabellings

Conventions (Brunck–Stade–Yehudayoff, "Depth Two for Simplices", Section 2):

* `Γ_n = {γ ∈ ℤ^{n+1} : ∑ γ = 0}` with coordinate vectors `u_0, …, u_n`.  We use the
  **reduced coordinates** `γ ↦ (γ_1, …, γ_n)` (the coordinate `γ_0 = -(γ_1 + ⋯ + γ_n)` is
  dropped): `Γ n := Fin n → ℤ`, and `reduceEquiv : {γ : Fin (n+1) → ℤ // ∑ γ = 0} ≃+ Γ n`
  is the corresponding isomorphism.  Coordinate `i : Fin n` of `Γ n` is the paper's
  coordinate `i + 1`.
* `vtx a` is the image of `u_a` under the coordinate projection (`vtx 0 = 0`,
  `vtx (i+1) = Pi.single i 1`), so that `t_{ab} = u_b - u_a` has reduced coordinates
  `rootVec ⟨a, b, _⟩ = vtx b - vtx a` (`reduceEquiv_root`).
* `Root n` is the set of pairs `(a, b)` with `a < b` in `Fin (n+1)`, ordered
  **lexicographically**.  `eRoot i = (0, i+1)` are the roots `t_{0,i+1}` (the paper's
  `E_{i+1} = e_{0,i+1}`).
* For an increasing map `f : Fin (n+1) → Fin (m+1)`, `latticeMap f : Γ n →+ Γ m` is the linear
  relabelling `t_{ab} ↦ t_{f a, f b}` (`latticeMap_rootVec`; no affine shift), and
  `rootEmb f hf : Root n ↪ Root m` is `(a, b) ↦ (f a, f b)` (strictly monotone).
* `succAbove_comp_succAbove` is the cosimplicial identity
  `ι_{q+1} ∘ ι_p = ι_p ∘ ι_q` for `p ≤ q`, with `ι_j = Fin.succAbove j`.
-/

open BigOperators

namespace MaxNN.ParamidChain

/-- The root lattice `Γ_n`, in reduced coordinates `(γ_1, …, γ_n)`. -/
abbrev Γ (n : ℕ) := Fin n → ℤ

/-- `vtx a`: reduced coordinates of the unit vector `u_a` (`vtx 0 = 0`). -/
def vtx {n : ℕ} (a : Fin (n + 1)) : Γ n := Fin.cases (0 : Γ n) (fun i => (Pi.single i 1 : Γ n)) a

@[simp] theorem vtx_zero {n : ℕ} : vtx (0 : Fin (n + 1)) = 0 := by
  simp [vtx]

@[simp] theorem vtx_succ {n : ℕ} (i : Fin n) : vtx i.succ = Pi.single i 1 := by
  simp [vtx]

/-! ### Reduced coordinates -/

/-- The sum-zero sublattice `{γ ∈ ℤ^{n+1} : ∑ γ = 0}`. -/
def sumZero (n : ℕ) : AddSubgroup (Fin (n + 1) → ℤ) where
  carrier := {γ | ∑ i, γ i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Pi.neg_apply, Finset.sum_neg_distrib] at *
    rw [ha, neg_zero]

/-- Reduced coordinates: `(γ_0, …, γ_n) ↦ (γ_1, …, γ_n)` is an isomorphism from the sum-zero
lattice onto `Γ n`; the inverse puts `γ_0 = -(γ_1 + ⋯ + γ_n)`. -/
def reduceEquiv (n : ℕ) : sumZero n ≃+ Γ n where
  toFun γ := fun i => (γ : Fin (n + 1) → ℤ) i.succ
  invFun δ := ⟨Fin.cons (-∑ i, δ i) δ, by
    show ∑ i, (Fin.cons (-∑ i, δ i) δ : Fin (n + 1) → ℤ) i = 0
    rw [Fin.sum_univ_succ]
    simp⟩
  left_inv γ := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · have h : ∑ i, (γ : Fin (n + 1) → ℤ) i = 0 := γ.2
      rw [Fin.sum_univ_succ] at h
      simp only [Fin.cons_zero]
      linarith
    · simp only [Fin.cons_succ]
  right_inv δ := by
    funext i
    simp only [Fin.cons_succ]
  map_add' γ δ := by
    funext i
    rfl

theorem reduceEquiv_root {n : ℕ} (a b : Fin (n + 1)) :
    reduceEquiv n ⟨Pi.single b 1 - Pi.single a 1, by
      show ∑ i, (Pi.single b 1 - Pi.single a 1 : Fin (n + 1) → ℤ) i = 0
      simp [Finset.sum_sub_distrib]⟩ = vtx b - vtx a := by
  funext i
  show (Pi.single b 1 - Pi.single a 1 : Fin (n + 1) → ℤ) i.succ = (vtx b - vtx a) i
  simp only [Pi.sub_apply]
  congr 1
  · refine Fin.cases ?_ (fun j => ?_) b
    · simp [Pi.single_apply, (Fin.succ_ne_zero i)]
    · simp [Pi.single_apply, Fin.succ_inj]
  · refine Fin.cases ?_ (fun j => ?_) a
    · simp [Pi.single_apply, (Fin.succ_ne_zero i)]
    · simp [Pi.single_apply, Fin.succ_inj]

/-! ### Roots -/

/-- A positive root `t_{ab} = u_b - u_a`, `a < b`. -/
structure Root (n : ℕ) where
  /-- first index -/
  a : Fin (n + 1)
  /-- second index -/
  b : Fin (n + 1)
  /-- `a < b` -/
  lt : a < b

namespace Root

variable {n : ℕ}

theorem ext' {r s : Root n} (ha : r.a = s.a) (hb : r.b = s.b) : r = s := by
  cases r
  cases s
  simp only at ha hb
  subst ha
  subst hb
  rfl

/-- The lexicographic key `(a, b)`. -/
def key (r : Root n) : Lex (Fin (n + 1) × Fin (n + 1)) := toLex (r.a, r.b)

theorem key_injective : Function.Injective (key : Root n → Lex (Fin (n + 1) × Fin (n + 1))) := by
  intro r s h
  have h' : (r.a, r.b) = (s.a, s.b) := toLex.injective h
  exact ext' (congrArg Prod.fst h') (congrArg Prod.snd h')

/-- Roots are ordered lexicographically. -/
instance : LinearOrder (Root n) := LinearOrder.lift' key key_injective

theorem lt_iff {r s : Root n} : r < s ↔ r.a < s.a ∨ (r.a = s.a ∧ r.b < s.b) :=
  Prod.Lex.lt_iff (r.a, r.b) (s.a, s.b)

theorem b_ne_zero (r : Root n) : r.b ≠ 0 :=
  Fin.pos_iff_ne_zero.1 (lt_of_le_of_lt (Fin.zero_le r.a) r.lt)

end Root

/-- The vector `t_{ab} = vtx b - vtx a ∈ Γ n` of a root. -/
def rootVec {n : ℕ} (r : Root n) : Γ n := vtx r.b - vtx r.a

/-- The root `t_{0,i+1}` (the paper's `E_{i+1}`). -/
def eRoot {n : ℕ} (i : Fin n) : Root n := ⟨0, i.succ, Fin.succ_pos i⟩

/-- The root `t_{0c}` through a vertex `c ≠ 0`. -/
def eAt {n : ℕ} (c : Fin (n + 1)) (hc : c ≠ 0) : Root n := ⟨0, c, Fin.pos_iff_ne_zero.2 hc⟩

theorem rootVec_eRoot {n : ℕ} (i : Fin n) : rootVec (eRoot i) = Pi.single i 1 := by
  simp [rootVec, eRoot]

theorem rootVec_eAt {n : ℕ} (c : Fin (n + 1)) (hc : c ≠ 0) : rootVec (eAt c hc) = vtx c := by
  simp [rootVec, eAt]

theorem rootVec_of_a_eq_zero {n : ℕ} {r : Root n} (h : r.a = 0) : rootVec r = vtx r.b := by
  simp [rootVec, h]

theorem eRoot_injective {n : ℕ} : Function.Injective (eRoot : Fin n → Root n) := by
  intro i j h
  exact Fin.succ_injective _ (congrArg Root.b h)

theorem eq_eRoot_of_a_eq_zero {n : ℕ} {r : Root n} (h : r.a = 0) :
    r = eRoot (r.b.pred r.b_ne_zero) :=
  Root.ext' (by simp [eRoot, h]) (by simp [eRoot])

theorem eAt_eq_eRoot {n : ℕ} (c : Fin (n + 1)) (hc : c ≠ 0) : eAt c hc = eRoot (c.pred hc) :=
  Root.ext' rfl (by simp [eRoot, eAt])

/-! ### Face relabellings -/

/-- The linear relabelling `Γ n →+ Γ m`, `t_{0,i+1} ↦ t_{f 0, f (i+1)}`; on all roots it is
`t_{ab} ↦ t_{f a, f b}` (`latticeMap_rootVec`). -/
def latticeMap {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) : Γ n →+ Γ m where
  toFun γ := ∑ i : Fin n, γ i • (vtx (f i.succ) - vtx (f 0))
  map_zero' := by simp
  map_add' γ δ := by simp [add_smul, Finset.sum_add_distrib]

theorem latticeMap_single {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (i : Fin n) :
    latticeMap f (Pi.single i 1) = vtx (f i.succ) - vtx (f 0) := by
  show ∑ j : Fin n, (Pi.single i 1 : Γ n) j • (vtx (f j.succ) - vtx (f 0)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem latticeMap_vtx {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (a : Fin (n + 1)) :
    latticeMap f (vtx a) = vtx (f a) - vtx (f 0) := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp
  · rw [vtx_succ, latticeMap_single]

theorem latticeMap_sub_vtx {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (a b : Fin (n + 1)) :
    latticeMap f (vtx b - vtx a) = vtx (f b) - vtx (f a) := by
  rw [AddMonoidHom.map_sub, latticeMap_vtx, latticeMap_vtx]
  abel

theorem latticeMap_comp {n m k : ℕ} (g : Fin (m + 1) → Fin (k + 1)) (f : Fin (n + 1) → Fin (m + 1))
    (γ : Γ n) : latticeMap g (latticeMap f γ) = latticeMap (g ∘ f) γ := by
  show latticeMap g (∑ i : Fin n, γ i • (vtx (f i.succ) - vtx (f 0))) =
    ∑ i : Fin n, γ i • (vtx (g (f i.succ)) - vtx (g (f 0)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AddMonoidHom.map_zsmul, latticeMap_sub_vtx]

/-- The root relabelling `(a, b) ↦ (f a, f b)` for strictly monotone `f`. -/
def rootEmb {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : StrictMono f) : Root n ↪ Root m where
  toFun r := ⟨f r.a, f r.b, hf r.lt⟩
  inj' := by
    intro r s h
    have h1 : f r.a = f s.a := congrArg Root.a h
    have h2 : f r.b = f s.b := congrArg Root.b h
    exact Root.ext' (hf.injective h1) (hf.injective h2)

@[simp] theorem rootEmb_a {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : StrictMono f)
    (r : Root n) : (rootEmb f hf r).a = f r.a := rfl

@[simp] theorem rootEmb_b {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : StrictMono f)
    (r : Root n) : (rootEmb f hf r).b = f r.b := rfl

theorem rootEmb_strictMono {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : StrictMono f) :
    StrictMono (rootEmb f hf) := by
  intro r s h
  rw [Root.lt_iff] at h ⊢
  simp only [rootEmb_a, rootEmb_b]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (hf h)
  · exact Or.inr ⟨by rw [h1], hf h2⟩

theorem rootVec_rootEmb {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : StrictMono f)
    (r : Root n) : rootVec (rootEmb f hf r) = latticeMap f (rootVec r) := by
  simp only [rootVec, rootEmb_a, rootEmb_b]
  rw [latticeMap_sub_vtx]

theorem rootEmb_comp {n m k : ℕ} (g : Fin (m + 1) → Fin (k + 1)) (hg : StrictMono g)
    (f : Fin (n + 1) → Fin (m + 1)) (hf : StrictMono f) (r : Root n) :
    rootEmb g hg (rootEmb f hf r) = rootEmb (g ∘ f) (hg.comp hf) r := rfl

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < p then (i : ℕ) else i + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp

/-- The cosimplicial identity `ι_{q+1} ∘ ι_p = ι_p ∘ ι_q` (`p ≤ q`), `ι_j = Fin.succAbove j`. -/
theorem succAbove_comp_succAbove {n : ℕ} {p q : Fin (n + 2)} (h : p ≤ q) :
    q.succ.succAbove ∘ p.succAbove = (Fin.castSucc p).succAbove ∘ q.succAbove := by
  funext k
  have h' : (p : ℕ) ≤ q := h
  apply Fin.ext
  simp only [Function.comp_apply, val_succAbove, Fin.val_succ, Fin.coe_castSucc]
  split_ifs <;> omega

end MaxNN.ParamidChain
