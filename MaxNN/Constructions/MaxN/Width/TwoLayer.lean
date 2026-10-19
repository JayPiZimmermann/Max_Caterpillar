import MaxNN.Constructions.MaxN.Width.Size.OneLayer
import MaxNN.Constructions.MaxN.Width.Layer.Coeffs
import MaxNN.Constructions.MaxN.Width.Class

/-! # Two-hidden-layer width bookkeeping -/

namespace MaxNN.Width

open BigOperators

variable {n : ℕ}

def TwoLayerWidth (n h₁ h₂ : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (T₁ : Affine n h₁) (T₂ : Affine h₁ h₂) (M : ReLUNet h₂ 1 0),
    (ReLUNet.layer T₁ (ReLUNet.layer T₂ M)).Computes f

theorem TwoLayerWidth.firstWidth {h₁ h₂ : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : TwoLayerWidth n h₁ h₂ f) : TwoLayerFirstWidth n h₁ f := by
  obtain ⟨T₁, T₂, M, hM⟩ := hf
  exact ⟨T₁, ReLUNet.layer T₂ M, hM⟩

def PairFacW (n w : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ F : (Fin (W n) → ℝ) → ℝ, OneLayerWidth (W n) w F ∧ ∀ x, f x = F (feat n x)}

theorem twoLayerWidth_of_pairFacW {w : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : f ∈ PairFacW n w) :
    TwoLayerWidth n (W n) w f := by
  obtain ⟨F, ⟨T, M, hM⟩, hfF⟩ := hf
  refine ⟨featureLayer n, T, M, fun x => ?_⟩
  rw [ReLUNet.eval_layer]
  rw [show (fun k => relu ((featureLayer n).eval x k)) = feat n x from rfl]
  have e : (ReLUNet.layer T M).eval (feat n x) 0 = F (feat n x) := hM (feat n x)
  rw [e]
  exact (hfF x).symm

theorem add_mem_pairFacW {w₁ w₂ : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ PairFacW n w₁) (hg : g ∈ PairFacW n w₂) :
    (fun x => f x + g x) ∈ PairFacW n (w₁ + w₂) := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  refine ⟨fun y => F y + G y, oneLayerWidth_add hF hG, fun x => ?_⟩
  show f x + g x = F (feat n x) + G (feat n x)
  rw [hfF x, hgG x]

theorem smul_mem_pairFacW {w : ℕ} {f : (Fin n → ℝ) → ℝ} (c : ℝ) (hf : f ∈ PairFacW n w) :
    (fun x => c * f x) ∈ PairFacW n w := by
  obtain ⟨F, hF, hfF⟩ := hf
  refine ⟨fun y => c * F y, oneLayerWidth_smul c hF, fun x => ?_⟩
  change c * f x = c * F (feat n x)
  rw [hfF x]

theorem zero_mem_pairFacW : (fun _ : Fin n → ℝ => (0 : ℝ)) ∈ PairFacW n 0 :=
  ⟨fun _ => 0, oneLayerWidth_zero (W n), fun _ => rfl⟩

theorem sum_mem_pairFacW {ι : Type _} [DecidableEq ι] {w : ℕ} (s : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (hF : ∀ i ∈ s, F i ∈ PairFacW n w) :
    (fun x => ∑ i in s, F i x) ∈ PairFacW n (s.card * w) := by
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (zero_mem_pairFacW (n := n))
  · intro a s ha ih hF
    rw [show (insert a s).card * w = w + s.card * w from by
      rw [Finset.card_insert_of_not_mem ha, add_mul, one_mul, Nat.add_comm]]
    rw [show (fun x : Fin n → ℝ => ∑ i in insert a s, F i x) =
      fun x => F a x + ∑ i in s, F i x from funext fun x => Finset.sum_insert ha]
    exact add_mem_pairFacW (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end MaxNN.Width
