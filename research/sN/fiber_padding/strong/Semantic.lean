import research.sN.fiber_padding.Paths

/-! # Semantic redundancy of a hidden neuron, and the paths that remove it

For an arbitrary `Network N h₁ h₂` we name the functions computed inside the network:

* `act₁ net j x`  : output of first-hidden-layer neuron `j`,
* `pre₂ net k x`  : preactivation of second-hidden-layer neuron `k`,
* `act₂ net k x`  : output of second-hidden-layer neuron `k`.

`FirstDependent net j'` : the function `act₁ net j'` is an affine combination (with a
constant term) of the functions `act₁ net j`, `j ≠ j'`.
`SecondDependent net k'` : the same for `act₂`.
`SecondActiveAbsorb net k k'` : `k ≠ k'`, both neurons are active at every input, the output
weight of `k'` is `s` times the output weight of `k`, and `pre₂ k + s * pre₂ k'` is bounded
below (automatic with bound `0` when `s ≥ 0`).

For each of the three we give an explicit continuous path of networks computing the same
function, ending in a network in which the neuron has zero outgoing weights.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Padding.Strong

open BigOperators MaxCaterpillar.Fiber.Padding

variable {N h₁ h₂ : ℕ}

/-- Output of first-hidden-layer neuron `j` at input `x`. -/
noncomputable def act₁ (net : Network N h₁ h₂) (j : Fin h₁) (x : Point N) : ℝ :=
  relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)

/-- Preactivation of second-hidden-layer neuron `k` at input `x`. -/
noncomputable def pre₂ (net : Network N h₁ h₂) (k : Fin h₂) (x : Point N) : ℝ :=
  (∑ j, net.W₂ k j * act₁ net j x) + net.b₂ k

/-- Output of second-hidden-layer neuron `k` at input `x`. -/
noncomputable def act₂ (net : Network N h₁ h₂) (k : Fin h₂) (x : Point N) : ℝ :=
  relu (pre₂ net k x)

theorem eval_eq (net : Network N h₁ h₂) (x : Point N) :
    net.eval x = (∑ k, net.w₃ k * act₂ net k x) + net.b₃ := rfl

theorem relu_nonneg' (t : ℝ) : 0 ≤ relu t := le_max_left 0 t

theorem relu_of_nonneg {t : ℝ} (h : 0 ≤ t) : relu t = t := max_eq_right h

theorem relu_of_nonpos {t : ℝ} (h : t ≤ 0) : relu t = 0 := max_eq_left h

/-! ## The semantic predicates -/

/-- The output function of first-hidden-layer neuron `j'` is an affine combination of the
output functions of the other first-hidden-layer neurons. -/
def FirstDependent (net : Network N h₁ h₂) (j' : Fin h₁) : Prop :=
  ∃ (c : Fin h₁ → ℝ) (c₀ : ℝ), c j' = 0 ∧
    ∀ x, act₁ net j' x = (∑ j, c j * act₁ net j x) + c₀

/-- The output function of second-hidden-layer neuron `k'` is an affine combination of the
output functions of the other second-hidden-layer neurons. -/
def SecondDependent (net : Network N h₁ h₂) (k' : Fin h₂) : Prop :=
  ∃ (c : Fin h₂ → ℝ) (c₀ : ℝ), c k' = 0 ∧
    ∀ x, act₂ net k' x = (∑ k, c k * act₂ net k x) + c₀

/-- Two distinct second-hidden-layer neurons that are active at every input, such that the
neuron `k` can absorb `k'`: the output weight of `k'` is `s` times that of `k` and
`pre₂ k + s * pre₂ k'` is bounded below by `-M`. -/
def SecondActiveAbsorb (net : Network N h₁ h₂) (k k' : Fin h₂) : Prop :=
  k ≠ k' ∧ (∀ x, 0 ≤ pre₂ net k x) ∧ (∀ x, 0 ≤ pre₂ net k' x) ∧
    ∃ s M : ℝ, net.w₃ k' = s * net.w₃ k ∧ ∀ x, 0 ≤ pre₂ net k x + s * pre₂ net k' x + M

/-! ## Transfer in the first hidden layer -/

/-- Move the fraction `t` of the outgoing weights of first-hidden-layer neuron `j'` to the
other neurons (coefficients `c`) and to the second-layer biases (coefficient `c₀`). -/
def transferFirst (net : Network N h₁ h₂) (j' : Fin h₁) (c : Fin h₁ → ℝ) (c₀ t : ℝ) :
    Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ k j := net.W₂ k j + t * (net.W₂ k j' * (c j - if j = j' then 1 else 0))
  b₂ k := net.b₂ k + t * (net.W₂ k j' * c₀)
  w₃ := net.w₃
  b₃ := net.b₃

theorem transferFirst_pre₂ (net : Network N h₁ h₂) (j' : Fin h₁) (c : Fin h₁ → ℝ) (c₀ t : ℝ)
    (hrel : ∀ x, act₁ net j' x = (∑ j, c j * act₁ net j x) + c₀) (k : Fin h₂) (x : Point N) :
    pre₂ (transferFirst net j' c c₀ t) k x = pre₂ net k x := by
  have hterm : ∀ j, (net.W₂ k j + t * (net.W₂ k j' * (c j - if j = j' then 1 else 0))) *
      act₁ net j x = net.W₂ k j * act₁ net j x + (t * net.W₂ k j') * (c j * act₁ net j x) -
        (t * net.W₂ k j') * (if j = j' then act₁ net j x else 0) := by
    intro j
    split_ifs <;> ring
  change (∑ j, (net.W₂ k j + t * (net.W₂ k j' * (c j - if j = j' then 1 else 0))) *
      act₁ net j x) + (net.b₂ k + t * (net.W₂ k j' * c₀)) =
    (∑ j, net.W₂ k j * act₁ net j x) + net.b₂ k
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hrel x]
  ring

theorem transferFirst_eval (net : Network N h₁ h₂) (j' : Fin h₁) (c : Fin h₁ → ℝ) (c₀ t : ℝ)
    (hrel : ∀ x, act₁ net j' x = (∑ j, c j * act₁ net j x) + c₀) (x : Point N) :
    (transferFirst net j' c c₀ t).eval x = net.eval x := by
  rw [eval_eq, eval_eq]
  have : ∀ k, act₂ (transferFirst net j' c c₀ t) k x = act₂ net k x := fun k => by
    unfold act₂
    rw [transferFirst_pre₂ net j' c c₀ t hrel k x]
  simp only [this]
  rfl

theorem transferFirst_zero (net : Network N h₁ h₂) (j' : Fin h₁) (c : Fin h₁ → ℝ) (c₀ : ℝ) :
    transferFirst net j' c c₀ 0 = net := by
  cases net
  simp [transferFirst]

theorem continuous_transferFirst (net : Network N h₁ h₂) (j' : Fin h₁) (c : Fin h₁ → ℝ)
    (c₀ : ℝ) : Continuous (fun t : ℝ => transferFirst net j' c c₀ t) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, ?_, continuous_const, continuous_const⟩
  · exact continuous_pi fun k => continuous_pi fun j =>
      continuous_const.add (continuous_id.mul continuous_const)
  · exact continuous_pi fun k => continuous_const.add (continuous_id.mul continuous_const)

theorem transferFirst_one_outDead (net : Network N h₁ h₂) (j' : Fin h₁) (c : Fin h₁ → ℝ)
    (c₀ : ℝ) (hc : c j' = 0) : FirstOutDead (transferFirst net j' c c₀ 1) j' := by
  intro k
  change net.W₂ k j' + 1 * (net.W₂ k j' * (c j' - if j' = j' then 1 else 0)) = 0
  rw [hc, if_pos rfl]
  ring

/-! ## Transfer in the second hidden layer -/

/-- Move the fraction `t` of the outgoing weight of second-hidden-layer neuron `k'` to the
other neurons (coefficients `c`) and to the output bias (coefficient `c₀`). -/
def transferSecond (net : Network N h₁ h₂) (k' : Fin h₂) (c : Fin h₂ → ℝ) (c₀ t : ℝ) :
    Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ := net.W₂
  b₂ := net.b₂
  w₃ k := net.w₃ k + t * (net.w₃ k' * (c k - if k = k' then 1 else 0))
  b₃ := net.b₃ + t * (net.w₃ k' * c₀)

theorem transferSecond_eval (net : Network N h₁ h₂) (k' : Fin h₂) (c : Fin h₂ → ℝ) (c₀ t : ℝ)
    (hrel : ∀ x, act₂ net k' x = (∑ k, c k * act₂ net k x) + c₀) (x : Point N) :
    (transferSecond net k' c c₀ t).eval x = net.eval x := by
  have hterm : ∀ k, (net.w₃ k + t * (net.w₃ k' * (c k - if k = k' then 1 else 0))) *
      act₂ net k x = net.w₃ k * act₂ net k x + (t * net.w₃ k') * (c k * act₂ net k x) -
        (t * net.w₃ k') * (if k = k' then act₂ net k x else 0) := by
    intro k
    split_ifs <;> ring
  rw [eval_eq, eval_eq]
  change (∑ k, (net.w₃ k + t * (net.w₃ k' * (c k - if k = k' then 1 else 0))) *
      act₂ net k x) + (net.b₃ + t * (net.w₃ k' * c₀)) =
    (∑ k, net.w₃ k * act₂ net k x) + net.b₃
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hrel x]
  ring

theorem transferSecond_zero (net : Network N h₁ h₂) (k' : Fin h₂) (c : Fin h₂ → ℝ) (c₀ : ℝ) :
    transferSecond net k' c c₀ 0 = net := by
  cases net
  simp [transferSecond]

theorem continuous_transferSecond (net : Network N h₁ h₂) (k' : Fin h₂) (c : Fin h₂ → ℝ)
    (c₀ : ℝ) : Continuous (fun t : ℝ => transferSecond net k' c c₀ t) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, continuous_const, continuous_const, ?_, ?_⟩
  · exact continuous_pi fun k => continuous_const.add (continuous_id.mul continuous_const)
  · exact continuous_const.add (continuous_id.mul continuous_const)

theorem transferSecond_one_outDead (net : Network N h₁ h₂) (k' : Fin h₂) (c : Fin h₂ → ℝ)
    (c₀ : ℝ) (hc : c k' = 0) : SecondOutDead (transferSecond net k' c c₀ 1) k' := by
  change net.w₃ k' + 1 * (net.w₃ k' * (c k' - if k' = k' then 1 else 0)) = 0
  rw [hc, if_pos rfl]
  ring

/-! ## Absorbing an always-active second-hidden-layer neuron into another one -/

/-- Neuron `k` absorbs the fraction `t` of the affine function of neuron `k'`
(`W₂ k += t s W₂ k'`, `b₂ k += t (s b₂ k' + M)`), the output weight of `k'` is multiplied
by `1 - t`, and the constant `t M w₃ k` is removed from the output bias. -/
def absorbSecond (net : Network N h₁ h₂) (k k' : Fin h₂) (s M t : ℝ) : Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ κ j := net.W₂ κ j + if κ = k then t * (s * net.W₂ k' j) else 0
  b₂ κ := net.b₂ κ + if κ = k then t * (s * net.b₂ k' + M) else 0
  w₃ κ := if κ = k' then (1 - t) * net.w₃ κ else net.w₃ κ
  b₃ := net.b₃ - t * (M * net.w₃ k)

theorem absorbSecond_pre₂_self (net : Network N h₁ h₂) (k k' : Fin h₂) (s M t : ℝ)
    (x : Point N) :
    pre₂ (absorbSecond net k k' s M t) k x = pre₂ net k x + t * (s * pre₂ net k' x + M) := by
  change (∑ j, (net.W₂ k j + if k = k then t * (s * net.W₂ k' j) else 0) * act₁ net j x) +
      (net.b₂ k + if k = k then t * (s * net.b₂ k' + M) else 0) =
    (∑ j, net.W₂ k j * act₁ net j x) + net.b₂ k +
      t * (s * ((∑ j, net.W₂ k' j * act₁ net j x) + net.b₂ k') + M)
  have hterm : ∀ j, (net.W₂ k j + t * (s * net.W₂ k' j)) * act₁ net j x =
      net.W₂ k j * act₁ net j x + (t * s) * (net.W₂ k' j * act₁ net j x) := fun j => by ring
  simp only [if_true, hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem absorbSecond_pre₂_of_ne (net : Network N h₁ h₂) (k k' : Fin h₂) (s M t : ℝ)
    {κ : Fin h₂} (hκ : κ ≠ k) (x : Point N) :
    pre₂ (absorbSecond net k k' s M t) κ x = pre₂ net κ x := by
  change (∑ j, (net.W₂ κ j + if κ = k then t * (s * net.W₂ k' j) else 0) * act₁ net j x) +
      (net.b₂ κ + if κ = k then t * (s * net.b₂ k' + M) else 0) =
    (∑ j, net.W₂ κ j * act₁ net j x) + net.b₂ κ
  simp only [if_neg hκ, add_zero]

theorem absorbSecond_eval (net : Network N h₁ h₂) (k k' : Fin h₂) (s M t : ℝ)
    (hkk : k ≠ k') (hk : ∀ x, 0 ≤ pre₂ net k x) (hk' : ∀ x, 0 ≤ pre₂ net k' x)
    (hw : net.w₃ k' = s * net.w₃ k) (hM : ∀ x, 0 ≤ pre₂ net k x + s * pre₂ net k' x + M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Point N) :
    (absorbSecond net k k' s M t).eval x = net.eval x := by
  classical
  have hpos : 0 ≤ pre₂ net k x + t * (s * pre₂ net k' x + M) := by
    have h1 := mul_nonneg (sub_nonneg.mpr ht1) (hk x)
    have h2 := mul_nonneg ht0 (hM x)
    nlinarith
  have hact : ∀ κ, act₂ (absorbSecond net k k' s M t) κ x =
      act₂ net κ x + if κ = k then t * (s * pre₂ net k' x + M) else 0 := by
    intro κ
    unfold act₂
    by_cases hκ : κ = k
    · subst hκ
      rw [absorbSecond_pre₂_self, if_pos rfl, relu_of_nonneg hpos, relu_of_nonneg (hk x)]
    · rw [absorbSecond_pre₂_of_ne net k k' s M t hκ, if_neg hκ, add_zero]
  have hterm : ∀ κ, (if κ = k' then (1 - t) * net.w₃ κ else net.w₃ κ) *
      (act₂ net κ x + if κ = k then t * (s * pre₂ net k' x + M) else 0) =
      net.w₃ κ * act₂ net κ x - (if κ = k' then t * (net.w₃ κ * act₂ net κ x) else 0) +
        (if κ = k then net.w₃ κ * (t * (s * pre₂ net k' x + M)) else 0) := by
    intro κ
    by_cases h1 : κ = k'
    · have h2 : κ ≠ k := fun h => hkk (h.symm.trans h1)
      rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2]
      ring
    · by_cases h2 : κ = k
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
        ring
  rw [eval_eq, eval_eq]
  simp only [hact]
  change (∑ κ, (if κ = k' then (1 - t) * net.w₃ κ else net.w₃ κ) *
      (act₂ net κ x + if κ = k then t * (s * pre₂ net k' x + M) else 0)) +
      (net.b₃ - t * (M * net.w₃ k)) = (∑ κ, net.w₃ κ * act₂ net κ x) + net.b₃
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hk'act : act₂ net k' x = pre₂ net k' x := relu_of_nonneg (hk' x)
  rw [hk'act, hw]
  ring

theorem absorbSecond_zero (net : Network N h₁ h₂) (k k' : Fin h₂) (s M : ℝ) :
    absorbSecond net k k' s M 0 = net := by
  cases net
  simp [absorbSecond]

theorem continuous_absorbSecond (net : Network N h₁ h₂) (k k' : Fin h₂) (s M : ℝ) :
    Continuous (fun t : ℝ => absorbSecond net k k' s M t) := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun κ => continuous_pi fun j => continuous_const.add ?_
    split_ifs
    · exact continuous_id.mul continuous_const
    · exact continuous_const
  · refine continuous_pi fun κ => continuous_const.add ?_
    split_ifs
    · exact continuous_id.mul continuous_const
    · exact continuous_const
  · refine continuous_pi fun κ => ?_
    change Continuous (fun t : ℝ => if κ = k' then (1 - t) * net.w₃ κ else net.w₃ κ)
    split_ifs
    · exact (continuous_const.sub continuous_id).mul continuous_const
    · exact continuous_const
  · exact continuous_const.sub (continuous_id.mul continuous_const)

theorem absorbSecond_one_outDead (net : Network N h₁ h₂) (k k' : Fin h₂) (s M : ℝ) :
    SecondOutDead (absorbSecond net k k' s M 1) k' := by
  change (if k' = k' then (1 - 1) * net.w₃ k' else net.w₃ k') = 0
  rw [if_pos rfl]
  ring

end MaxCaterpillar.Fiber.Padding.Strong
