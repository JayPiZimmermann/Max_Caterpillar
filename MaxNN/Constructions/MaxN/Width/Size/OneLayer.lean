import MaxNN.Core.Class

/-!
# One hidden layer, with its width in the type

`OneLayerWidth h w F` says `F : ℝ^h → ℝ` is computed by a ReLU network with **one** hidden layer
of **exactly `w`** units.  This is the second layer of a certificate network: it reads the
pair-feature output (`Width/Layer/Features.lean`) and must produce the certificate.

The closure lemmas track the width arithmetic that `Core/Class.lean` throws away:

* `oneLayerWidth_reluLin` — one `relu` of a linear form: **1** unit;
* `oneLayerWidth_linComb` — running two nets in parallel **adds** the widths;
* `oneLayerWidth_smul` — scaling is free (it happens in the output layer);
* `sum_oneLayerWidth` — a sum over a `Finset` costs `card × width`;
* `oneLayerWidth_maxLin` — **a `max` of two linear forms costs 3 units**
  (`max a b = relu (a - b) + relu b - relu (-b)`).

That last one is the atom of a certificate, and `Width/Size.lean` multiplies it up.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Width

open BigOperators

/-- The `1 × 1` affine row `y ↦ c * y 0`. -/
noncomputable def scaleRow (c : ℝ) : Affine 1 1 where
  A := fun _ _ => c
  b := fun _ => 0

theorem scaleRow_eval (c : ℝ) (y : Fin 1 → ℝ) : (scaleRow c).eval y 0 = c * y 0 := by
  show (∑ _j : Fin 1, c * y 0) + (0 : ℝ) = c * y 0
  rw [Fin.sum_univ_one, add_zero]

/-- **`F : ℝ^h → ℝ` is computed by a ReLU network with one hidden layer of exactly `w` units.** -/
def OneLayerWidth (h w : ℕ) (F : (Fin h → ℝ) → ℝ) : Prop :=
  ∃ (T : Affine h w) (M : ReLUNet w 1 0), (ReLUNet.layer T M).Computes F

theorem oneLayerWidth_congr {h w : ℕ} {F G : (Fin h → ℝ) → ℝ} (hFG : ∀ y, F y = G y)
    (hF : OneLayerWidth h w F) : OneLayerWidth h w G := by
  obtain ⟨T, M, hM⟩ := hF
  exact ⟨T, M, fun y => by rw [hM y, hFG y]⟩

/-- **One `relu` of a linear form: one unit.** -/
theorem oneLayerWidth_reluLin {h : ℕ} (a : Fin h → ℝ) :
    OneLayerWidth h 1 (fun y => relu (∑ k, a k * y k)) := by
  refine ⟨⟨fun _ => a, fun _ => 0⟩, ReLUNet.affine ⟨fun _ _ => 1, fun _ => 0⟩, fun y => ?_⟩
  rw [ReLUNet.eval_layer, ReLUNet.eval_affine]
  show (∑ _j : Fin 1, (1 : ℝ) * relu ((∑ k, a k * y k) + 0)) + (0 : ℝ)
      = relu (∑ k, a k * y k)
  rw [Fin.sum_univ_one, add_zero, one_mul, add_zero]

/-- The empty hidden layer computes the zero function. -/
theorem oneLayerWidth_zero (h : ℕ) : OneLayerWidth h 0 (fun _ => (0 : ℝ)) := by
  refine ⟨⟨fun i => i.elim0, fun i => i.elim0⟩,
    ReLUNet.affine ⟨fun _ i => i.elim0, fun _ => 0⟩, fun y => ?_⟩
  rw [ReLUNet.eval_layer, ReLUNet.eval_affine]
  show (∑ j : Fin 0, (Fin.elim0 j : ℝ)) + (0 : ℝ) = 0
  rw [Fin.sum_univ_zero, add_zero]

/-- **Running two nets in parallel adds the hidden widths.** -/
theorem oneLayerWidth_linComb {h w₁ w₂ : ℕ} {F G : (Fin h → ℝ) → ℝ} (c₁ c₂ : ℝ)
    (hF : OneLayerWidth h w₁ F) (hG : OneLayerWidth h w₂ G) :
    OneLayerWidth h (w₁ + w₂) (fun y => c₁ * F y + c₂ * G y) := by
  obtain ⟨T₁, M₁, h₁⟩ := hF
  obtain ⟨T₂, M₂, h₂⟩ := hG
  refine ⟨T₁.stack T₂,
    ((M₁.precomp (Affine.projFst w₁ w₂)).pair
      (M₂.precomp (Affine.projSnd w₁ w₂))).postcomp (Affine.row2 c₁ c₂), fun y => ?_⟩
  rw [ReLUNet.eval_layer, ReLUNet.postcomp_eval, ReLUNet.pair_eval, Affine.row2_eval,
    Fin.append_left, Fin.append_right, ReLUNet.precomp_eval, ReLUNet.precomp_eval]
  have hFst : (Affine.projFst w₁ w₂).eval (fun i => relu ((T₁.stack T₂).eval y i))
      = fun i => relu (T₁.eval y i) := by
    funext i
    rw [Affine.projFst_eval, Affine.stack_eval_castAdd]
  have hSnd : (Affine.projSnd w₁ w₂).eval (fun i => relu ((T₁.stack T₂).eval y i))
      = fun i => relu (T₂.eval y i) := by
    funext i
    rw [Affine.projSnd_eval, Affine.stack_eval_natAdd]
  rw [hFst, hSnd]
  have e₁ : M₁.eval (fun i => relu (T₁.eval y i)) 0 = F y := h₁ y
  have e₂ : M₂.eval (fun i => relu (T₂.eval y i)) 0 = G y := h₂ y
  rw [e₁, e₂]

theorem oneLayerWidth_add {h w₁ w₂ : ℕ} {F G : (Fin h → ℝ) → ℝ}
    (hF : OneLayerWidth h w₁ F) (hG : OneLayerWidth h w₂ G) :
    OneLayerWidth h (w₁ + w₂) (fun y => F y + G y) := by
  refine oneLayerWidth_congr (fun y => ?_) (oneLayerWidth_linComb 1 1 hF hG)
  rw [one_mul, one_mul]

/-- **Scaling is free**: it is absorbed into the output layer. -/
theorem oneLayerWidth_smul {h w : ℕ} {F : (Fin h → ℝ) → ℝ} (c : ℝ)
    (hF : OneLayerWidth h w F) : OneLayerWidth h w (fun y => c * F y) := by
  obtain ⟨T, M, hM⟩ := hF
  refine ⟨T, M.postcomp (scaleRow c), fun y => ?_⟩
  rw [ReLUNet.eval_layer, ReLUNet.postcomp_eval, scaleRow_eval]
  have e : M.eval (fun i => relu (T.eval y i)) 0 = F y := hM y
  rw [e]

/-- **A sum over a `Finset` costs `card × width`.**  This is the mechanism by which the
symmetrisation over all `n!` orderings inflates the SECOND layer. -/
theorem sum_oneLayerWidth {ι : Type _} [DecidableEq ι] {h w : ℕ} (s : Finset ι)
    (F : ι → (Fin h → ℝ) → ℝ) (hF : ∀ i ∈ s, OneLayerWidth h w (F i)) :
    OneLayerWidth h (s.card * w) (fun y => ∑ i in s, F i y) := by
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [show (∅ : Finset ι).card * w = 0 from by rw [Finset.card_empty, Nat.zero_mul]]
    rw [show (fun y : Fin h → ℝ => ∑ i in (∅ : Finset ι), F i y) = (fun _ => (0 : ℝ)) from
      funext fun y => Finset.sum_empty]
    exact oneLayerWidth_zero h
  · intro a s ha ih hF
    rw [show (insert a s).card * w = w + s.card * w from by
      rw [Finset.card_insert_of_not_mem ha, add_mul, one_mul]
      exact Nat.add_comm _ _]
    rw [show (fun y : Fin h → ℝ => ∑ i in insert a s, F i y)
        = (fun y => F a y + ∑ i in s, F i y) from funext fun y => Finset.sum_insert ha]
    exact oneLayerWidth_add (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- **THE ATOM: a `max` of two linear forms costs exactly three second-layer units.**
`max a b = relu (a - b) + relu b - relu (-b)`. -/
theorem oneLayerWidth_maxLin {h : ℕ} (a b : Fin h → ℝ) :
    OneLayerWidth h 3 (fun y => max (∑ k, a k * y k) (∑ k, b k * y k)) := by
  have h1 : OneLayerWidth h 1 (fun y => relu (∑ k, (a k - b k) * y k)) :=
    oneLayerWidth_reluLin _
  have h2 : OneLayerWidth h 1 (fun y => relu (∑ k, b k * y k)) := oneLayerWidth_reluLin _
  have h3 : OneLayerWidth h 1 (fun y => relu (∑ k, (-(b k)) * y k)) := oneLayerWidth_reluLin _
  have hall := oneLayerWidth_linComb (1 : ℝ) 1 h1 (oneLayerWidth_linComb (1 : ℝ) (-1) h2 h3)
  rw [show (3 : ℕ) = 1 + (1 + 1) from by decide]
  refine oneLayerWidth_congr (fun y => ?_) hall
  have hab : (∑ k, (a k - b k) * y k) = (∑ k, a k * y k) - (∑ k, b k * y k) := by
    rw [Finset.sum_congr rfl fun k _ => sub_mul (a k) (b k) (y k), Finset.sum_sub_distrib]
  have hnb : (∑ k, (-(b k)) * y k) = -(∑ k, b k * y k) := by
    rw [Finset.sum_congr rfl fun k _ => neg_mul (b k) (y k), Finset.sum_neg_distrib]
  rw [hab, hnb, one_mul, one_mul, one_mul, neg_one_mul]
  have hrelu := relu_sub_relu_neg (∑ k, b k * y k)
  have hmax := max_eq_relu_add (∑ k, b k * y k) (∑ k, a k * y k)
  rw [max_comm (∑ k, a k * y k) (∑ k, b k * y k)]
  rw [hmax]
  linarith

end Width

end MaxNN
