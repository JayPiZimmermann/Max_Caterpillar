import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Normalize
import MaxNN.Constructions.Paramid.Caterpillar.Words.Crossing

/-!
# Full coordinates for reduced caterpillar keys

The dictionary keys of `Corrections` live in reduced simplex coordinates
`Fin (r + 1) → ℝ`, pulled back along `coordT`, `(coordT y)_i = y_{i+1} - y_0`.
For counting arguments it is convenient to read a key in the full
coordinates `y_0, …, y_{r+1}`.  A reduced vector `v` corresponds to the full
vector `fullVec v = (-(∑ v), v)`, which has coordinate sum zero and satisfies
`⟨v, coordT y⟩ = ⟨fullVec v, y⟩` (`dot_coordT_eq_fullVec`).

For a key `k = (γ, V)` we define
* the full head `keyHead k = fullVec γ`;
* the pair predicate `HasPair k i j`: the label `u_i - u_j` (whose unit is
  `σ(y_i - y_j)`) belongs to `V`;
* the upper neighbours `N⁺(o) = {x > o : HasPair k o x}`;
* `κ_o = h_o + |N⁺(o)|` (`kappa`);
* the pair set `M = {(i, j) : i < j, HasPair k i j}` (`pairSet`).

The only general fact proved here is `Σ_o κ_o = |M|` (`sum_kappa`).
-/

open BigOperators

namespace MaxCaterpillar.CountCubic

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain

/-- The full-coordinate vector of a reduced vector. -/
def fullVec {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun o => @Fin.cases n (fun _ => ℝ) (-(∑ i, v i)) (fun i => v i) o

section FullVec

variable {n : ℕ}

@[simp] theorem fullVec_zero_apply (v : Fin n → ℝ) : fullVec v 0 = -(∑ i, v i) := rfl

@[simp] theorem fullVec_succ_apply (v : Fin n → ℝ) (i : Fin n) : fullVec v i.succ = v i := rfl

theorem fullVec_add (u v : Fin n → ℝ) : fullVec (u + v) = fullVec u + fullVec v := by
  funext o
  refine Fin.cases ?_ (fun i => ?_) o
  · simp only [fullVec_zero_apply, Pi.add_apply, Finset.sum_add_distrib, neg_add]
  · simp only [fullVec_succ_apply, Pi.add_apply]

theorem fullVec_neg (v : Fin n → ℝ) : fullVec (-v) = -fullVec v := by
  funext o
  refine Fin.cases ?_ (fun i => ?_) o
  · simp only [fullVec_zero_apply, Pi.neg_apply, Finset.sum_neg_distrib]
  · simp only [fullVec_succ_apply, Pi.neg_apply]

theorem fullVec_sub (u v : Fin n → ℝ) : fullVec (u - v) = fullVec u - fullVec v := by
  rw [sub_eq_add_neg, fullVec_add, fullVec_neg, ← sub_eq_add_neg]

theorem fullVec_zero : fullVec (0 : Fin n → ℝ) = 0 := by
  funext o
  refine Fin.cases ?_ (fun _ => ?_) o
  · simp only [fullVec_zero_apply, Pi.zero_apply, Finset.sum_const_zero, neg_zero]
  · simp only [fullVec_succ_apply, Pi.zero_apply]

theorem fullVec_sum {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    fullVec (∑ x in s, f x) = ∑ x in s, fullVec (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, fullVec_zero]
  | insert ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fullVec_add, ih]

/-- Full vectors have coordinate sum zero. -/
theorem sum_fullVec (v : Fin n → ℝ) : ∑ o, fullVec v o = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [fullVec_zero_apply, fullVec_succ_apply, neg_add_self]

/-- `fullVec` is the full-coordinate form of the pulled-back linear functional. -/
theorem dot_coordT_eq_fullVec (v : Fin n → ℝ) (y : Fin (n + 1) → ℝ) :
    dot v ((CoordAux.coordT n).mulVec y) = ∑ o, fullVec v o * y o := by
  rw [MaxNN.Width.dot_coordT, Fin.sum_univ_succ]
  simp only [fullVec_zero_apply, fullVec_succ_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

/-- The full vector of the simplex vertex `u_a` is `e_a - e_0`. -/
theorem fullVec_toR_vtx_apply (a o : Fin (n + 1)) :
    fullVec (toR (vtx a)) o = (if a = o then 1 else 0) - (if (0 : Fin (n + 1)) = o then 1 else 0) := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp only [vtx_zero, sub_self]
    refine Fin.cases ?_ (fun _ => ?_) o
    · simp [toR]
    · simp [toR]
  · refine Fin.cases ?_ (fun l => ?_) o
    · simp only [fullVec_zero_apply, vtx_succ, toR, if_true]
      rw [if_neg (Fin.succ_ne_zero i)]
      simp [Pi.single_apply]
    · simp only [fullVec_succ_apply, vtx_succ, toR]
      rw [if_neg (Ne.symm (Fin.succ_ne_zero l))]
      by_cases h : i = l
      · subst h
        simp
      · rw [if_neg (fun e => h (Fin.succ_injective _ e))]
        simp [Pi.single_apply, Ne.symm h]

/-- The full vector of the simplex difference `u_a - u_b` is `e_a - e_b`. -/
theorem fullVec_vtx_sub_apply (a b o : Fin (n + 1)) :
    fullVec (toR (vtx a) - toR (vtx b)) o = (if a = o then 1 else 0) - (if b = o then 1 else 0) := by
  rw [fullVec_sub, Pi.sub_apply, fullVec_toR_vtx_apply, fullVec_toR_vtx_apply]
  ring

end FullVec

section Keys

variable {r : ℕ}

/-- The head of a key in full coordinates `y_0, …, y_{r+1}`. -/
noncomputable def keyHead (k : RealKey (r + 1)) : Fin (r + 1 + 1) → ℝ := fullVec k.1

/-- The key contains the label `u_i - u_j`, i.e. the function `σ(y_i - y_j)`. -/
def HasPair (k : RealKey (r + 1)) (i j : Fin (r + 1 + 1)) : Prop :=
  toR (vtx i) - toR (vtx j) ∈ k.2

/-- Upper neighbours `N⁺(o) = {x > o : (o, x) ∈ M}`. -/
noncomputable def upNbrs (k : RealKey (r + 1)) (o : Fin (r + 1 + 1)) :
    Finset (Fin (r + 1 + 1)) := by
  classical
  exact Finset.univ.filter fun x => o < x ∧ HasPair k o x

/-- `κ_o = h_o + |N⁺(o)|`. -/
noncomputable def kappa (k : RealKey (r + 1)) (o : Fin (r + 1 + 1)) : ℝ :=
  keyHead k o + (upNbrs k o).card

/-- The pair set `M = {(i, j) : i < j, σ(y_i - y_j) is a label}`. -/
noncomputable def pairSet (k : RealKey (r + 1)) : Finset (Fin (r + 1 + 1) × Fin (r + 1 + 1)) := by
  classical
  exact Finset.univ.filter fun p => p.1 < p.2 ∧ HasPair k p.1 p.2

theorem mem_upNbrs {k : RealKey (r + 1)} {o x : Fin (r + 1 + 1)} :
    x ∈ upNbrs k o ↔ o < x ∧ HasPair k o x := by
  classical
  unfold upNbrs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_pairSet {k : RealKey (r + 1)} {p : Fin (r + 1 + 1) × Fin (r + 1 + 1)} :
    p ∈ pairSet k ↔ p.1 < p.2 ∧ HasPair k p.1 p.2 := by
  classical
  unfold pairSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem keyHead_sum (k : RealKey (r + 1)) : ∑ o, keyHead k o = 0 := sum_fullVec k.1

/-- Each pair of `M` is counted once, at its lower end. -/
theorem sum_card_upNbrs (k : RealKey (r + 1)) :
    ∑ o, (upNbrs k o).card = (pairSet k).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro o _
  have he : (pairSet k).filter (fun p => p.1 = o) = (upNbrs k o).image (Prod.mk o) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, mem_pairSet, Finset.mem_image, mem_upNbrs, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hab, hp⟩, rfl⟩
      exact ⟨b, ⟨hab, hp⟩, rfl, rfl⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl, rfl⟩
      exact ⟨⟨hx, hp⟩, rfl⟩
  rw [he, Finset.card_image_of_injective _ (Prod.mk.inj_left o)]

/-- `Σ_o κ_o = |M|` for every key (the head has coordinate sum zero). -/
theorem sum_kappa (k : RealKey (r + 1)) : ∑ o, kappa k o = (pairSet k).card := by
  unfold kappa
  rw [Finset.sum_add_distrib, keyHead_sum, zero_add, ← Nat.cast_sum, sum_card_upNbrs]

end Keys

end MaxCaterpillar.CountCubic
