import MaxNN.Constructions.MaxN.Width.TwoLayer
import MaxNN.Constructions.Paramid.Geom.Coordinates

/-!
# Paramid units in the pair-feature layer

Module L9 of `work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md` (Section 8.1,
Group C); the dense-skip normal form is `Paramid/DenseSkip.lean`.

The coordinate change is compiled through the pair-feature layer `feat` of
`Width/Layer/Features.lean`. Contents:

* `PairLin` is closed under negation, differences and finite sums (`pairLinSubmodule`), and
  contains every hinge `relu (x b − x a)` (`relu_sub_mem_pairLin`);
* `relu_mem_pairFacW_of_pairLin`: the `relu` of a pair-linear function costs one second-layer
  unit; `mem_pairFacW_two_of_pairLin`: a pair-linear function costs two
  (`f = relu f − relu (−f)`);
* `TwoLayerWidth.mono_right`: idle units may be added to the second hidden layer;
-/

namespace MaxNN

namespace Width

open BigOperators MaxNN.ParamidChain

variable {N : ℕ}

/-! ## `PairLin`: negation, differences, finite sums, hinges of coordinate differences -/

theorem neg_mem_pairLin {f : (Fin N → ℝ) → ℝ} (hf : f ∈ PairLin N) :
    (fun x => -f x) ∈ PairLin N := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k => -a k, fun x => ?_⟩
  show -f x = ∑ k, -a k * feat N x k
  rw [ha x, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => (neg_mul (a k) (feat N x k)).symm

theorem sub_mem_pairLin {f g : (Fin N → ℝ) → ℝ} (hf : f ∈ PairLin N) (hg : g ∈ PairLin N) :
    (fun x => f x - g x) ∈ PairLin N := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun k => a k - b k, fun x => ?_⟩
  show f x - g x = ∑ k, (a k - b k) * feat N x k
  rw [ha x, hb x, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (sub_mul (a k) (b k) (feat N x k)).symm

theorem sum_mem_pairLin {ι : Type*} (s : Finset ι) (F : ι → (Fin N → ℝ) → ℝ)
    (hF : ∀ i ∈ s, F i ∈ PairLin N) : (fun x => ∑ i in s, F i x) ∈ PairLin N := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x : Fin N → ℝ => ∑ i in (∅ : Finset ι), F i x) = fun _ => (0 : ℝ) := by
      funext x
      exact Finset.sum_empty
    rw [e]
    exact zero_mem_pairLin
  · intro a s ha ih hF
    have e : (fun x : Fin N → ℝ => ∑ i in insert a s, F i x) =
        fun x => F a x + ∑ i in s, F i x := by
      funext x
      exact Finset.sum_insert ha
    rw [e]
    exact add_mem_pairLin (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- `PairLin N` as a submodule of the functions `ℝ^N → ℝ`. -/
def pairLinSubmodule (N : ℕ) : Submodule ℝ ((Fin N → ℝ) → ℝ) where
  carrier := PairLin N
  add_mem' := fun hf hg => add_mem_pairLin hf hg
  zero_mem' := zero_mem_pairLin
  smul_mem' := fun c _ hf => smul_mem_pairLin c hf

theorem mem_pairLinSubmodule {f : (Fin N → ℝ) → ℝ} : f ∈ pairLinSubmodule N ↔ f ∈ PairLin N :=
  Iff.rfl

/-- A hinge on a coordinate difference is pair-linear:
`relu (x b − x a) = max (x a) (x b) − x a`. -/
theorem relu_sub_mem_pairLin (a b : Fin N) :
    (fun x : Fin N → ℝ => relu (x b - x a)) ∈ PairLin N := by
  have e : (fun x : Fin N → ℝ => relu (x b - x a)) = fun x => max (x a) (x b) - x a := by
    funext x
    rw [max_eq_relu_add (x a) (x b)]
    ring
  rw [e]
  exact sub_mem_pairLin (pairMax_mem_pairLin a b) (coord_mem_pairLin a)

/-! ## Second-layer cost of pair-linear functions and of their `relu` -/

/-- **The `relu` of a pair-linear function costs one second-layer unit.** -/
theorem relu_mem_pairFacW_of_pairLin {f : (Fin N → ℝ) → ℝ} (hf : f ∈ PairLin N) :
    (fun x => relu (f x)) ∈ PairFacW N 1 := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun y => relu (∑ k, a k * y k), oneLayerWidth_reluLin a, fun x => ?_⟩
  show relu (f x) = relu (∑ k, a k * feat N x k)
  rw [ha x]

/-- **A pair-linear function costs two second-layer units**: `f = relu f − relu (−f)`. -/
theorem mem_pairFacW_two_of_pairLin {f : (Fin N → ℝ) → ℝ} (hf : f ∈ PairLin N) :
    f ∈ PairFacW N 2 := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun y => 1 * relu (∑ k, a k * y k) + (-1) * relu (∑ k, (-a k) * y k),
    oneLayerWidth_linComb 1 (-1) (oneLayerWidth_reluLin a)
      (oneLayerWidth_reluLin fun k => -a k), fun x => ?_⟩
  show f x = 1 * relu (∑ k, a k * feat N x k) + (-1) * relu (∑ k, (-a k) * feat N x k)
  have hn : (∑ k, (-a k) * feat N x k) = -(∑ k, a k * feat N x k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => neg_mul (a k) (feat N x k)
  rw [hn, ← ha x, one_mul, neg_one_mul, ← sub_eq_add_neg, relu_sub_relu_neg]

/-- **Idle second-layer units**: a network of second width `h₂` is one of every second width
`h₂' ≥ h₂` (the extra units are zero rows that the output layer ignores). -/
theorem TwoLayerWidth.mono_right {n h₁ h₂ h₂' : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : TwoLayerWidth n h₁ h₂ f) (h : h₂ ≤ h₂') : TwoLayerWidth n h₁ h₂' f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨T₁, T₂, M, hM⟩ := hf
  refine ⟨T₁, T₂.stack ⟨fun _ _ => 0, fun _ => 0⟩, M.precomp (Affine.projFst h₂ d),
    fun x => ?_⟩
  rw [ReLUNet.eval_layer, ReLUNet.eval_layer, ReLUNet.precomp_eval]
  have e : (Affine.projFst h₂ d).eval (fun i => relu ((T₂.stack ⟨fun _ _ => 0, fun _ => 0⟩).eval
      (fun k => relu (T₁.eval x k)) i)) =
      fun i => relu (T₂.eval (fun k => relu (T₁.eval x k)) i) := by
    funext i
    rw [Affine.projFst_eval, Affine.stack_eval_castAdd]
  rw [e]
  have hx := hM x
  rw [ReLUNet.eval_layer, ReLUNet.eval_layer] at hx
  exact hx

/-! ## The coordinate change -/

/-- Precomposition with `coordT n`, as a linear map on function spaces. -/
noncomputable def coordPull (n : ℕ) : ((Fin n → ℝ) → ℝ) →ₗ[ℝ] ((Fin (n + 1) → ℝ) → ℝ) :=
  LinearMap.funLeft ℝ ℝ (ParamidGeom.CoordAux.coordT n).mulVec

@[simp] theorem coordPull_apply (n : ℕ) (f : (Fin n → ℝ) → ℝ) (y : Fin (n + 1) → ℝ) :
    coordPull n f y = f ((ParamidGeom.CoordAux.coordT n).mulVec y) :=
  rfl

/-- `⟨c, coordT n y⟩ = ∑_i c_i (y_{i+1} − y_0)`. -/
theorem dot_coordT (n : ℕ) (c : Fin n → ℝ) (y : Fin (n + 1) → ℝ) :
    dot c ((ParamidGeom.CoordAux.coordT n).mulVec y) = ∑ i, c i * (y i.succ - y 0) := by
  rw [ParamidGeom.CoordAux.coordT_mulVec]
  rfl

/-- `⟨vtx c, coordT n y⟩ = y_c − y_0`. -/
theorem dot_toR_vtx_coordT (n : ℕ) (c : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    dot (ParamidGeom.toR (vtx c)) ((ParamidGeom.CoordAux.coordT n).mulVec y) = y c - y 0 := by
  rw [dot_coordT]
  refine Fin.cases ?_ (fun j => ?_) c
  · rw [vtx_zero, sub_self]
    refine Finset.sum_eq_zero fun i _ => ?_
    show (((0 : Γ n) i : ℤ) : ℝ) * (y i.succ - y 0) = 0
    rw [Pi.zero_apply, Int.cast_zero, zero_mul]
  · rw [vtx_succ, Finset.sum_eq_single j]
    · show (((Pi.single j 1 : Γ n) j : ℤ) : ℝ) * (y j.succ - y 0) = y j.succ - y 0
      rw [Pi.single_eq_same, Int.cast_one, one_mul]
    · intro i _ hij
      show (((Pi.single j 1 : Γ n) i : ℤ) : ℝ) * (y i.succ - y 0) = 0
      rw [Pi.single_eq_of_ne hij, Int.cast_zero, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

theorem dot_coordT_mem_pairLin (n : ℕ) (c : Fin n → ℝ) :
    (fun y : Fin (n + 1) → ℝ => dot c ((ParamidGeom.CoordAux.coordT n).mulVec y)) ∈
      PairLin (n + 1) := by
  have e : (fun y : Fin (n + 1) → ℝ => dot c ((ParamidGeom.CoordAux.coordT n).mulVec y)) =
      fun y => ∑ i, c i * (y i.succ - y 0) := funext fun y => dot_coordT n c y
  rw [e]
  exact sum_mem_pairLin Finset.univ (fun i y => c i * (y i.succ - y 0)) fun i _ =>
    smul_mem_pairLin (c i) (sub_mem_pairLin (coord_mem_pairLin i.succ) (coord_mem_pairLin 0))


end Width

end MaxNN
