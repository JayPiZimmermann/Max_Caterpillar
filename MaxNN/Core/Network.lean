import MaxNN.Core.Relu
import MaxNN.Core.Affine

/-!
# ReLU networks as finite data

`ReLUNet m n k` is a ReLU network from `ℝ^m` to `ℝ^n` with **exactly `k` hidden layers**:

* `affine T` is a bare output affine map — depth one, no hidden layer;
* `layer T N` prepends one hidden layer — apply the affine map `T`, apply `relu`
  componentwise, feed the result to `N`.

An inhabitant of `ReLUNet m n k` is therefore precisely the finite data
`T⁽¹⁾, …, T⁽ᵏ⁺¹⁾` of `k + 1` affine maps between explicit finite-dimensional spaces, and
`eval` is the alternating composition `T⁽ᵏ⁺¹⁾ ∘ relu ∘ T⁽ᵏ⁾ ∘ ⋯ ∘ relu ∘ T⁽¹⁾`.  Making
the hidden-layer count a type index turns "this network has `k` hidden layers" into a
fact checked by the kernel, not a side condition.

Network surgery (each operation comes with its `eval` and depth bookkeeping):

* `precomp` / `postcomp` — affine pre- and post-composition costs no hidden layers;
* `pair` — run two networks of equal depth in parallel on a common input;
* `deepen` / `padBy` — insert identity hidden layers via `x = relu x - relu (-x)`,
  so shallower networks embed into deeper classes;
* `addReluLayer` — append one hidden layer at the output end.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

/-- A ReLU network from `ℝ^m` to `ℝ^n` with exactly `k` hidden layers, as finite data:
`affine T` is the output affine map, `layer T N` prepends a hidden layer (affine map `T`
followed by a componentwise `relu`). -/
inductive ReLUNet : ℕ → ℕ → ℕ → Type where
  | affine {m n : ℕ} (T : Affine m n) : ReLUNet m n 0
  | layer {m h n k : ℕ} (T : Affine m h) (N : ReLUNet h n k) : ReLUNet m n (k + 1)

namespace ReLUNet

/-- The function a network computes: the alternating composition
`T⁽ᵏ⁺¹⁾ ∘ relu ∘ T⁽ᵏ⁾ ∘ ⋯ ∘ relu ∘ T⁽¹⁾`. -/
noncomputable def eval : {m n k : ℕ} → ReLUNet m n k → (Fin m → ℝ) → Fin n → ℝ
  | _, _, _, affine T, x => T.eval x
  | _, _, _, layer T N, x => N.eval fun i => relu (T.eval x i)

theorem eval_affine {m n : ℕ} (T : Affine m n) (x : Fin m → ℝ) :
    (affine T).eval x = T.eval x := rfl

theorem eval_layer {m h n k : ℕ} (T : Affine m h) (N : ReLUNet h n k) (x : Fin m → ℝ) :
    (layer T N).eval x = N.eval fun i => relu (T.eval x i) := rfl

/-- The number of hidden layers of a network is its depth index. -/
def hiddenLayers {m n k : ℕ} (_ : ReLUNet m n k) : ℕ := k

/-- `N.Computes f`: the network `N` computes the scalar function `f` exactly,
on all of `ℝ^n`. -/
def Computes {n k : ℕ} (N : ReLUNet n 1 k) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, N.eval x 0 = f x

/-! ## Affine pre- and post-composition (cost no hidden layers) -/

/-- Precompose with an affine map, folding it into the first layer. -/
noncomputable def precomp {m₀ : ℕ} : {m n k : ℕ} → ReLUNet m n k → Affine m₀ m →
    ReLUNet m₀ n k
  | _, _, _, affine T, S => affine (T.comp S)
  | _, _, _, layer T N, S => layer (T.comp S) N

theorem precomp_eval {m₀ m n k : ℕ} (N : ReLUNet m n k) (S : Affine m₀ m)
    (x : Fin m₀ → ℝ) : (N.precomp S).eval x = N.eval (S.eval x) := by
  cases N with
  | affine T => rw [show (affine T).precomp S = affine (T.comp S) from rfl,
      eval_affine, eval_affine, Affine.comp_eval]
  | layer T N => rw [show (layer T N).precomp S = layer (T.comp S) N from rfl,
      eval_layer, eval_layer, Affine.comp_eval]

/-- Postcompose with an affine map, folding it into the output layer. -/
noncomputable def postcomp : {m n k : ℕ} → ReLUNet m n k → {p : ℕ} → Affine n p →
    ReLUNet m p k
  | _, _, _, affine T, _, S => affine (S.comp T)
  | _, _, _, layer T N, _, S => layer T (N.postcomp S)

theorem postcomp_eval {m n k : ℕ} (N : ReLUNet m n k) {p : ℕ} (S : Affine n p)
    (x : Fin m → ℝ) : (N.postcomp S).eval x = S.eval (N.eval x) := by
  induction N with
  | affine T => rw [show (affine T).postcomp S = affine (S.comp T) from rfl,
      eval_affine, eval_affine, Affine.comp_eval]
  | layer T N ih => rw [show (layer T N).postcomp S = layer T (N.postcomp S) from rfl,
      eval_layer, eval_layer, ih]

/-! ## Parallel composition of equal-depth networks -/

/-- Run two networks of equal depth in parallel on a common input:
`(N₁.pair N₂).eval x = Fin.append (N₁.eval x) (N₂.eval x)`. -/
noncomputable def pair : {k m n₁ n₂ : ℕ} → ReLUNet m n₁ k → ReLUNet m n₂ k →
    ReLUNet m (n₁ + n₂) k
  | 0, _, _, _, affine T₁, affine T₂ => affine (T₁.stack T₂)
  | _ + 1, _, _, _, @layer _ h₁ _ _ T₁ N₁, @layer _ h₂ _ _ T₂ N₂ =>
      layer (T₁.stack T₂)
        ((N₁.precomp (Affine.projFst h₁ h₂)).pair (N₂.precomp (Affine.projSnd h₁ h₂)))

theorem pair_eval : ∀ {k m n₁ n₂ : ℕ} (N₁ : ReLUNet m n₁ k) (N₂ : ReLUNet m n₂ k)
    (x : Fin m → ℝ), (N₁.pair N₂).eval x = Fin.append (N₁.eval x) (N₂.eval x) := by
  intro k
  induction k with
  | zero =>
    intro m n₁ n₂ N₁ N₂ x
    cases N₁ with
    | affine T₁ =>
      cases N₂ with
      | affine T₂ =>
        rw [show (affine T₁).pair (affine T₂) = affine (T₁.stack T₂) from rfl,
          eval_affine, eval_affine, eval_affine, Affine.stack_eval]
  | succ k ih =>
    intro m n₁ n₂ N₁ N₂ x
    cases N₁ with
    | layer T₁ M₁ =>
      cases N₂ with
      | layer T₂ M₂ =>
        rw [show (layer T₁ M₁).pair (layer T₂ M₂)
            = layer (T₁.stack T₂)
              ((M₁.precomp (Affine.projFst _ _)).pair (M₂.precomp (Affine.projSnd _ _)))
            from rfl,
          eval_layer, ih, precomp_eval, precomp_eval, eval_layer, eval_layer]
        have hFst : (Affine.projFst _ _).eval
            (fun i => relu ((T₁.stack T₂).eval x i)) = fun i => relu (T₁.eval x i) := by
          funext i
          rw [Affine.projFst_eval, Affine.stack_eval_castAdd]
        have hSnd : (Affine.projSnd _ _).eval
            (fun i => relu ((T₁.stack T₂).eval x i)) = fun i => relu (T₂.eval x i) := by
          funext i
          rw [Affine.projSnd_eval, Affine.stack_eval_natAdd]
        rw [hFst, hSnd]

/-! ## Identity padding: shallower networks embed into deeper classes -/

/-- Insert one hidden layer computing the identity, via `x = relu x - relu (-x)`. -/
noncomputable def deepen {m n k : ℕ} (N : ReLUNet m n k) : ReLUNet m n (k + 1) :=
  layer ((Affine.id m).stack (Affine.id m).neg) (N.precomp (Affine.diffHalves m))

theorem deepen_eval {m n k : ℕ} (N : ReLUNet m n k) (x : Fin m → ℝ) :
    (deepen N).eval x = N.eval x := by
  unfold deepen
  rw [eval_layer, precomp_eval]
  have hx : (Affine.diffHalves m).eval
      (fun i => relu (((Affine.id m).stack (Affine.id m).neg).eval x i)) = x := by
    funext i
    rw [Affine.diffHalves_eval, Affine.stack_eval_castAdd, Affine.stack_eval_natAdd,
      Affine.neg_eval, Affine.id_eval, relu_sub_relu_neg]
  rw [hx]

/-- Pad a network with `d` identity hidden layers. -/
noncomputable def padBy {m n k : ℕ} : (d : ℕ) → ReLUNet m n k → ReLUNet m n (k + d)
  | 0, N => N
  | d + 1, N => deepen (padBy d N)

theorem padBy_eval {m n k : ℕ} (d : ℕ) (N : ReLUNet m n k) (x : Fin m → ℝ) :
    (padBy d N).eval x = N.eval x := by
  induction d with
  | zero => rfl
  | succ d ih => rw [show padBy (d + 1) N = deepen (padBy d N) from rfl, deepen_eval, ih]

/-! ## Appending one hidden layer at the output end -/

/-- Append a hidden layer at the output end: `relu` the outputs of `N`, then apply `T`. -/
noncomputable def addReluLayer : {m h k : ℕ} → ReLUNet m h k → {p : ℕ} → Affine h p →
    ReLUNet m p (k + 1)
  | _, _, _, affine S, _, T => layer S (affine T)
  | _, _, _, layer S N, _, T => layer S (N.addReluLayer T)

theorem addReluLayer_eval {m h k : ℕ} (N : ReLUNet m h k) {p : ℕ} (T : Affine h p)
    (x : Fin m → ℝ) :
    (N.addReluLayer T).eval x = T.eval fun i => relu (N.eval x i) := by
  induction N with
  | affine S => rfl
  | layer S N ih =>
      rw [show (layer S N).addReluLayer T = layer S (N.addReluLayer T) from rfl,
        eval_layer, ih, eval_layer]

/-! ## Sequential composition (hidden layers add) -/

/-- Sequential composition: feed the outputs of `N₁` (no `relu` in between — the output
affine map of `N₁` merges with the input affine map of `N₂`).  Hidden layers add. -/
noncomputable def seqComp : {m h j : ℕ} → ReLUNet m h j → {p k : ℕ} → ReLUNet h p k →
    ReLUNet m p (k + j)
  | _, _, _, affine T, _, _, N₂ => N₂.precomp T
  | _, _, _, layer T N₁, _, _, N₂ => layer T (N₁.seqComp N₂)

theorem seqComp_eval {m h j : ℕ} (N₁ : ReLUNet m h j) {p k : ℕ} (N₂ : ReLUNet h p k)
    (x : Fin m → ℝ) : (N₁.seqComp N₂).eval x = N₂.eval (N₁.eval x) := by
  induction N₁ with
  | affine T => rw [show (affine T).seqComp N₂ = N₂.precomp T from rfl, precomp_eval,
      eval_affine]
  | layer T N₁ ih => rw [show (layer T N₁).seqComp N₂ = layer T (N₁.seqComp N₂) from rfl,
      eval_layer, ih, eval_layer]

/-! ## Pairing a family of scalar networks of equal depth -/

/-- Run `p + 1` scalar networks of equal depth in parallel: output `i` is network `i`. -/
noncomputable def pairMany : {p : ℕ} → (∀ _ : Fin (p + 1), ReLUNet m 1 j) →
    ReLUNet m (p + 1) j
  | 0, N => N 0
  | _ + 1, N => (pairMany fun i => N i.castSucc).pair (N (Fin.last _))

theorem pairMany_eval {m j p : ℕ} (N : ∀ _ : Fin (p + 1), ReLUNet m 1 j) (x : Fin m → ℝ) :
    (pairMany N).eval x = fun i => (N i).eval x 0 := by
  induction p with
  | zero =>
    rw [show pairMany N = N 0 from rfl]
    funext i
    rw [show i = 0 from Fin.eq_zero i]
  | succ p ih =>
    rw [show pairMany N = (pairMany fun i => N i.castSucc).pair (N (Fin.last _)) from rfl,
      ReLUNet.pair_eval, ih]
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [show Fin.last (p + 1) = Fin.natAdd (p + 1) (0 : Fin 1) from Fin.ext rfl,
        Fin.append_right]
    · rw [show Fin.castSucc i = Fin.castAdd 1 i from rfl, Fin.append_left]
      rfl

end ReLUNet

end MaxNN
