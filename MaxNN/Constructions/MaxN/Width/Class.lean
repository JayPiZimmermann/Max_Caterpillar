import MaxNN.Constructions.MaxN.Width.Layer.Features

/-!
# Two hidden layers with a **bounded first layer**, and the pair-feature class

`ReLUClass n 2` forgets the widths.  `TwoLayerFirstWidth n h f` remembers the one that matters
here: `f` is computed, exactly on all of `ℝ^n`, by a network `ReLUNet.layer T M` with
`T : Affine n h` and `M : ReLUNet h 1 1` — two hidden layers, the **first of width `h`**.  The
width is visible in the *type*, so the bound is a genuine conclusion, not a side condition.

`PairFac n k` is the working notion: the functions that factor through the pair-feature layer
(`Width/Layer/Features.lean`) as a class-`k` function of its output.  It is a vector space
(`add_mem_pairFac`, `smul_mem_pairFac`, `sum_mem_pairFac`), it contains the coordinates and the
pairwise maxima at level `0`, a `max` of two of its level-`k` members is at level `k + 1`
(`max_mem_pairFac`) — and **every member of `PairFac n 1` has first-layer width `W n`**
(`firstWidth_of_pairFac_one`).  The whole content of the upper bound is that the grammar's
certificates land in `PairFac n 1`; that is `Width/Certificate.lean`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Width

open BigOperators

variable {n : ℕ}

/-- **`f` is computed by a ReLU network with exactly two hidden layers whose FIRST hidden layer
has `h` units.**  (The second layer's width is unconstrained.) -/
def TwoLayerFirstWidth (n h : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (T : Affine n h) (M : ReLUNet h 1 1), (ReLUNet.layer T M).Computes f

/-- A width-annotated network is in particular a two-hidden-layer network. -/
theorem TwoLayerFirstWidth.mem_reluClass_two {h : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : TwoLayerFirstWidth n h f) : f ∈ ReLUClass n 2 := by
  obtain ⟨T, M, hM⟩ := hf
  exact ⟨ReLUNet.layer T M, hM⟩

/-- Affine precomposition costs no hidden layer **and no first-layer width**: the affine map is
folded into the first layer's rows.  This is what makes width bounds transport along
coordinate duplications (`MAX m` from `MAX n`, `m ≤ n`). -/
theorem TwoLayerFirstWidth.precomp {m h : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : TwoLayerFirstWidth n h f) (S : Affine m n) :
    TwoLayerFirstWidth m h (fun x => f (S.eval x)) := by
  obtain ⟨T, M, hM⟩ := hf
  refine ⟨T.comp S, M, fun x => ?_⟩
  rw [ReLUNet.eval_layer]
  have e : (fun i => relu ((T.comp S).eval x i)) = fun i => relu (T.eval (S.eval x) i) := by
    funext i
    rw [Affine.comp_eval]
  rw [e]
  exact hM (S.eval x)

/-! ## Factoring through the pair-feature layer -/

/-- `PairFac n k` — the functions on `ℝ^n` that factor through the pair-feature layer
`feat n` as a class-`k` function of its `W n` outputs. -/
def PairFac (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ F : (Fin (W n) → ℝ) → ℝ, F ∈ ReLUClass (W n) k ∧ ∀ x, f x = F (feat n x) }

/-- **The width theorem, engine form.**  A function that factors through the pair-feature layer
as a ONE-hidden-layer function of its output is computed by a two-hidden-layer network whose
first layer is the pair-feature layer — of width `W n = n.choose 2 + 2 * n`, *whatever* the
function is. -/
theorem firstWidth_of_pairFac_one {f : (Fin n → ℝ) → ℝ} (hf : f ∈ PairFac n 1) :
    TwoLayerFirstWidth n (W n) f := by
  obtain ⟨F, ⟨M, hM⟩, hfF⟩ := hf
  refine ⟨featureLayer n, M, fun x => ?_⟩
  rw [ReLUNet.eval_layer]
  rw [show (fun k => relu ((featureLayer n).eval x k)) = feat n x from rfl]
  rw [hM (feat n x)]
  exact (hfF x).symm

/-! ## `PairFac n k` is a vector space, and `max` climbs one level -/

theorem pairFac_mono {k l : ℕ} (hkl : k ≤ l) : PairFac n k ⊆ PairFac n l := by
  rintro f ⟨F, hF, hfF⟩
  exact ⟨F, reluClass_mono hkl hF, hfF⟩

theorem const_mem_pairFac (n k : ℕ) (c : ℝ) : (fun _ : Fin n → ℝ => c) ∈ PairFac n k :=
  ⟨fun _ => c, reluClass_mono (Nat.zero_le k) (const_mem_reluClass c), fun _ => rfl⟩

theorem linComb_mem_pairFac {k : ℕ} {f g : (Fin n → ℝ) → ℝ} (c₁ c₂ : ℝ)
    (hf : f ∈ PairFac n k) (hg : g ∈ PairFac n k) :
    (fun x => c₁ * f x + c₂ * g x) ∈ PairFac n k := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  refine ⟨fun y => c₁ * F y + c₂ * G y, linComb_mem_reluClass c₁ c₂ hF hG, fun x => ?_⟩
  show c₁ * f x + c₂ * g x = c₁ * F (feat n x) + c₂ * G (feat n x)
  rw [hfF x, hgG x]

theorem add_mem_pairFac {k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ PairFac n k) (hg : g ∈ PairFac n k) : (fun x => f x + g x) ∈ PairFac n k := by
  have h := linComb_mem_pairFac 1 1 hf hg
  have e : (fun x : Fin n → ℝ => (1 : ℝ) * f x + 1 * g x) = fun x => f x + g x := by
    funext x
    rw [one_mul, one_mul]
  rw [e] at h
  exact h

theorem smul_mem_pairFac {k : ℕ} {f : (Fin n → ℝ) → ℝ} (c : ℝ) (hf : f ∈ PairFac n k) :
    (fun x => c * f x) ∈ PairFac n k := by
  have h := linComb_mem_pairFac c 0 hf hf
  have e : (fun x : Fin n → ℝ => c * f x + 0 * f x) = fun x => c * f x := by
    funext x
    rw [zero_mul, add_zero]
  rw [e] at h
  exact h

theorem sub_mem_pairFac {k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ PairFac n k) (hg : g ∈ PairFac n k) : (fun x => f x - g x) ∈ PairFac n k := by
  have h := linComb_mem_pairFac 1 (-1) hf hg
  have e : (fun x : Fin n → ℝ => (1 : ℝ) * f x + (-1) * g x) = fun x => f x - g x := by
    funext x
    rw [one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [e] at h
  exact h

theorem sum_mem_pairFac {ι : Type _} {k : ℕ} (s : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (hF : ∀ i ∈ s, F i ∈ PairFac n k) :
    (fun x => ∑ i in s, F i x) ∈ PairFac n k := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x : Fin n → ℝ => ∑ i in (∅ : Finset ι), F i x) = fun _ => (0 : ℝ) := by
      funext x
      exact Finset.sum_empty
    rw [e]
    exact const_mem_pairFac n k 0
  · intro a s ha ih hF
    have e : (fun x : Fin n → ℝ => ∑ i in insert a s, F i x)
        = fun x => F a x + ∑ i in s, F i x := by
      funext x
      exact Finset.sum_insert ha
    rw [e]
    exact add_mem_pairFac (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- **One `max` costs one hidden layer — and no first-layer width.** -/
theorem max_mem_pairFac {k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ PairFac n k) (hg : g ∈ PairFac n k) :
    (fun x => max (f x) (g x)) ∈ PairFac n (k + 1) := by
  obtain ⟨F, hF, hfF⟩ := hf
  obtain ⟨G, hG, hgG⟩ := hg
  refine ⟨fun y => max (F y) (G y), max_mem_reluClass hF hG, fun x => ?_⟩
  show max (f x) (g x) = max (F (feat n x)) (G (feat n x))
  rw [hfF x, hgG x]

/-! ## The generators at level `0` -/

/-- A coordinate is recovered from the layer output by a linear form. -/
theorem coord_mem_pairFac (i : Fin n) : (fun x : Fin n → ℝ => x i) ∈ PairFac n 0 :=
  ⟨fun y => coordLin i y, coordLin_mem i, fun x => (coordLin_feat x i).symm⟩

/-- **A pairwise maximum is recovered from the layer output by a linear form** — this is the
one shared `relu` unit per unordered pair, and it is why the first layer never grows. -/
theorem pairMax_mem_pairFac (i j : Fin n) :
    (fun x : Fin n → ℝ => max (x i) (x j)) ∈ PairFac n 0 :=
  ⟨fun y => pairMaxLin i j y, pairMaxLin_mem i j, fun x => (pairMaxLin_feat x i j).symm⟩

end Width

end MaxNN
