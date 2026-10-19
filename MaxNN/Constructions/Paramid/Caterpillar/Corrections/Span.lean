import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Keys
import MaxNN.Constructions.MaxN.Width.Paramid.Unit

/-!
# Face corrections as an ordinary two-hidden-layer network

This module keeps the oriented simplex differences used by caterpillar words.
Every cone face is either another paramid unit in the finite face-key
dictionary, or is already linear in the pair-feature layer.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidGeom.Faces MaxNN.Width

variable {n : ℕ}

/-- A real-key paramid unit, pulled back from reduced simplex coordinates. -/
noncomputable def realUnitY (k : RealKey n) (y : Fin (n + 1) → ℝ) : ℝ :=
  paramidOn k.1 k.2 ((CoordAux.coordT n).mulVec y)

/-- Its preactivation. -/
noncomputable def realUnitArg (k : RealKey n) (y : Fin (n + 1) → ℝ) : ℝ :=
  dot k.1 ((CoordAux.coordT n).mulVec y) +
    ∑ v in k.2, relu (dot v ((CoordAux.coordT n).mulVec y))

theorem realUnitY_eq_relu (k : RealKey n) (y : Fin (n + 1) → ℝ) :
    realUnitY k y = relu (realUnitArg k y) := rfl

theorem relu_dot_simplexDifference_mem_pairLin {v : Fin n → ℝ}
    (hv : IsSimplexDifference v) :
    (fun y : Fin (n + 1) → ℝ => relu (dot v ((CoordAux.coordT n).mulVec y))) ∈
      PairLin (n + 1) := by
  obtain ⟨a, b, rfl⟩ := hv
  have e : (fun y : Fin (n + 1) → ℝ =>
      relu (dot (toR (ParamidChain.vtx a) - toR (ParamidChain.vtx b))
        ((CoordAux.coordT n).mulVec y))) = fun y => relu (y a - y b) := by
    funext y
    rw [SupportCut.dot_sub_left, MaxNN.Width.dot_toR_vtx_coordT,
      MaxNN.Width.dot_toR_vtx_coordT]
    congr 1
    ring
  rw [e]
  exact relu_sub_mem_pairLin b a

/-- The outer preactivation is pair-linear when all labels are simplex differences. -/
theorem realUnitArg_mem_pairLin (k : RealKey n)
    (hk : ∀ v ∈ k.2, IsSimplexDifference v) :
    (fun y => realUnitArg k y) ∈ PairLin (n + 1) := by
  unfold realUnitArg
  exact add_mem_pairLin (MaxNN.Width.dot_coordT_mem_pairLin n k.1)
    (sum_mem_pairLin k.2
      (fun v y => relu (dot v ((CoordAux.coordT n).mulVec y)))
      (fun v hv => relu_dot_simplexDifference_mem_pairLin (hk v hv)))

/-- One real-key unit costs one neuron in the second hidden layer. -/
theorem realUnitY_mem_pairFacW (k : RealKey n)
    (hk : ∀ v ∈ k.2, IsSimplexDifference v) :
    (fun y => realUnitY k y) ∈ PairFacW (n + 1) 1 := by
  rw [show (fun y => realUnitY k y) = fun y => relu (realUnitArg k y) from
    funext (realUnitY_eq_relu k)]
  exact relu_mem_pairFacW_of_pairLin (realUnitArg_mem_pairLin k hk)

/-- Combinations over one finite real-key dictionary, with a pair-linear remainder. -/
def RealUnitSpan (n : ℕ) (K : Finset (RealKey n)) :
    Submodule ℝ ((Fin (n + 1) → ℝ) → ℝ) where
  carrier := {f | ∃ (c : RealKey n → ℝ) (r : (Fin (n + 1) → ℝ) → ℝ),
    r ∈ PairLin (n + 1) ∧ ∀ y, f y = ∑ k in K, c k * realUnitY k y + r y}
  zero_mem' := ⟨fun _ => 0, fun _ => 0, zero_mem_pairLin, fun y => by
    change (0 : ℝ) = ∑ k in K, (0 : ℝ) * realUnitY k y + 0
    rw [Finset.sum_congr rfl fun k _ => zero_mul (realUnitY k y), Finset.sum_const_zero,
      zero_add]⟩
  add_mem' := by
    rintro f g ⟨c₁, r₁, hr₁, h₁⟩ ⟨c₂, r₂, hr₂, h₂⟩
    refine ⟨fun k => c₁ k + c₂ k, fun y => r₁ y + r₂ y,
      add_mem_pairLin hr₁ hr₂, fun y => ?_⟩
    show f y + g y = ∑ k in K, (c₁ k + c₂ k) * realUnitY k y + (r₁ y + r₂ y)
    rw [h₁ y, h₂ y,
      Finset.sum_congr rfl fun k _ => add_mul (c₁ k) (c₂ k) (realUnitY k y),
      Finset.sum_add_distrib]
    ring
  smul_mem' := by
    rintro a f ⟨c, r, hr, h⟩
    refine ⟨fun k => a * c k, fun y => a * r y, smul_mem_pairLin a hr, fun y => ?_⟩
    show a * f y = ∑ k in K, (a * c k) * realUnitY k y + a * r y
    rw [h y, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => (mul_assoc a (c k) (realUnitY k y)).symm

theorem mem_realUnitSpan_iff {K : Finset (RealKey n)} {f : (Fin (n + 1) → ℝ) → ℝ} :
    f ∈ RealUnitSpan n K ↔
      ∃ (c : RealKey n → ℝ) (r : (Fin (n + 1) → ℝ) → ℝ),
        r ∈ PairLin (n + 1) ∧ ∀ y, f y = ∑ k in K, c k * realUnitY k y + r y :=
  Iff.rfl

theorem realUnitY_mem_realUnitSpan {K : Finset (RealKey n)} {k : RealKey n} (hk : k ∈ K) :
    (fun y => realUnitY k y) ∈ RealUnitSpan n K := by
  refine ⟨fun k' => if k' = k then 1 else 0, fun _ => 0, zero_mem_pairLin, fun y => ?_⟩
  rw [add_zero, Finset.sum_eq_single k]
  · change realUnitY k y = (if k = k then 1 else 0) * realUnitY k y
    rw [if_pos rfl, one_mul]
  · intro b _ hb
    change (if b = k then 1 else 0) * realUnitY b y = 0
    rw [if_neg hb, zero_mul]
  · exact fun hk' => absurd hk hk'

theorem pairLin_mem_realUnitSpan {K : Finset (RealKey n)}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : f ∈ PairLin (n + 1)) :
    f ∈ RealUnitSpan n K := by
  refine ⟨fun _ => 0, f, hf, fun y => ?_⟩
  rw [Finset.sum_congr rfl fun k _ => zero_mul (realUnitY k y), Finset.sum_const_zero,
    zero_add]

/-- Every member of a cone family is represented by its face-key dictionary
or by the pair-feature layer. -/
theorem hS_coord_mem_realUnitSpan_of_mem_coneFamily
    {K : Finset (RealKey n)} {γ : Fin n → ℝ} {V : Finset (Fin n → ℝ)}
    (hK : faceKeys γ V ⊆ K) (hV : ∀ v ∈ V, IsSimplexDifference v)
    {F : Finset (Fin n → ℝ)} (hF : F ∈ coneFamily γ V) :
    (fun y => hS F ((CoordAux.coordT n).mulVec y)) ∈ RealUnitSpan n K := by
  rcases hS_of_mem_coneFamily hF with
    ⟨P, Z, hP, hZ, hPZ, hFe⟩ | ⟨c, Z, hZ, hFe⟩ | hFe
  · rw [hFe]
    exact realUnitY_mem_realUnitSpan
      (hK (mem_faceKeys_of_disjoint hP hZ hPZ))
  · rw [hFe]
    exact pairLin_mem_realUnitSpan (add_mem_pairLin
      (MaxNN.Width.dot_coordT_mem_pairLin n c)
      (sum_mem_pairLin Z
        (fun v y => relu (dot v ((CoordAux.coordT n).mulVec y)))
        (fun v hv => relu_dot_simplexDifference_mem_pairLin (hV v (hZ hv)))))
  · rw [hFe]
    exact pairLin_mem_realUnitSpan zero_mem_pairLin

/-- A member of `RealUnitSpan` gives an ordinary layered ReLU network with
the standard pair-feature first layer and exactly `|K|+2` second-layer units. -/
theorem twoLayerWidth_of_mem_realUnitSpan {K : Finset (RealKey n)}
    (hK : ∀ k ∈ K, ∀ v ∈ k.2, IsSimplexDifference v)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : f ∈ RealUnitSpan n K) :
    TwoLayerWidth (n + 1) (W (n + 1)) (K.card + 2) f := by
  obtain ⟨c, r, hr, h⟩ := hf
  have hu := sum_mem_pairFacW K (fun k y => c k * realUnitY k y)
    (fun k hk => smul_mem_pairFacW (c k) (realUnitY_mem_pairFacW k (hK k hk)))
  have hall := add_mem_pairFacW hu (mem_pairFacW_two_of_pairLin hr)
  rw [Nat.mul_one] at hall
  apply twoLayerWidth_of_pairFacW
  rwa [show f = fun y => ∑ k in K, c k * realUnitY k y + r y from funext h]

end MaxNN.Caterpillar.Corrections
