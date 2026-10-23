import MaxCaterpillar.Definitions
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot

/-! # Width frontiers: basic tools

* `lin c x = Σ cᵢ xᵢ`, the diagonal `diag t = t·1`, and facts about `Maximum`.
* `ZNet`: a two-hidden-layer network without biases.
* The bias reduction (Hertrich–Basu–Di Summa–Skutella, Prop. 2.3): a network that computes
  a positively homogeneous function computes the same function after all biases are set
  to zero (`Network.eval_zeroBias_of_posHom`).
* Local odd linearity: `f (q + εv) - f (q - εv)` is linear in `v` for small `ε > 0`.
  One-hidden-layer functions have this property at every point, while the maximum does
  not have it at a point where at least three coordinates tie at the top
  (`not_locOddLin_max`). This replaces the gradient-jump argument of Lemma 0.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators Filter Topology

variable {N : ℕ}

/-! ## Linear forms -/

/-- The linear form `x ↦ Σ cᵢ xᵢ`. -/
def lin (c x : Point N) : ℝ := ∑ i, c i * x i

/-- The diagonal point `t·1`. -/
def diag (t : ℝ) : Point N := fun _ => t

/-- The `i`-th standard basis vector. -/
def unitVec (i : Fin N) : Point N := fun k => if k = i then 1 else 0

lemma lin_add_right (c x y : Point N) : lin c (x + y) = lin c x + lin c y := by
  simp only [lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma lin_smul_right (c x : Point N) (a : ℝ) : lin c (a • x) = a * lin c x := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma lin_neg_right (c x : Point N) : lin c (-x) = -lin c x := by
  simp only [lin, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

lemma lin_sub_right (c x y : Point N) : lin c (x - y) = lin c x - lin c y := by
  simp only [lin, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma lin_zero_right (c : Point N) : lin c 0 = 0 := by
  simp only [lin, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

lemma lin_add_left (c c' x : Point N) : lin (c + c') x = lin c x + lin c' x := by
  simp only [lin, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma lin_smul_left (c x : Point N) (a : ℝ) : lin (a • c) x = a * lin c x := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma lin_neg_left (c x : Point N) : lin (-c) x = -lin c x := by
  simp only [lin, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma lin_zero_left (x : Point N) : lin 0 x = 0 := by
  simp only [lin, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

lemma lin_sum_left {ι : Type*} (s : Finset ι) (c : ι → Point N) (x : Point N) :
    lin (∑ j in s, c j) x = ∑ j in s, lin (c j) x := by
  simp only [lin, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma lin_sum_right {ι : Type*} (s : Finset ι) (c : Point N) (x : ι → Point N) :
    lin c (∑ j in s, x j) = ∑ j in s, lin c (x j) := by
  simp only [lin, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma lin_diag (c : Point N) (t : ℝ) : lin c (diag t) = t * ∑ i, c i := by
  simp only [lin, diag, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma lin_unitVec (c : Point N) (i : Fin N) : lin c (unitVec i) = c i := by
  simp [lin, unitVec]

/-! ## The ReLU function -/

lemma relu_nonneg (u : ℝ) : 0 ≤ relu u := le_max_left _ _

lemma relu_of_nonneg {u : ℝ} (h : 0 ≤ u) : relu u = u := max_eq_right h

lemma relu_of_nonpos {u : ℝ} (h : u ≤ 0) : relu u = 0 := max_eq_left h

lemma relu_sub_relu_neg (u : ℝ) : relu u - relu (-u) = u := by
  rcases le_total 0 u with h | h
  · rw [relu_of_nonneg h, relu_of_nonpos (by linarith)]; ring
  · rw [relu_of_nonpos h, relu_of_nonneg (by linarith)]; ring

lemma relu_mul_pos {t : ℝ} (ht : 0 < t) (u : ℝ) : relu (t * u) = t * relu u := by
  unfold relu
  rw [mul_max_of_nonneg _ _ ht.le, mul_zero]

lemma continuous_relu : Continuous relu := continuous_const.max continuous_id

/-! ## The maximum -/

section Max

variable [NeZero N]

lemma le_Maximum (x : Point N) (i : Fin N) : x i ≤ Maximum N x :=
  Finset.le_sup' x (Finset.mem_univ i)

lemma Maximum_le_iff (x : Point N) (c : ℝ) : Maximum N x ≤ c ↔ ∀ i, x i ≤ c := by
  simp [Maximum, Finset.sup'_le_iff]

lemma exists_eq_Maximum (x : Point N) : ∃ i, Maximum N x = x i := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin N)) x
  exact ⟨i, h⟩

lemma Maximum_eq_of (x : Point N) (m : ℝ) (i : Fin N) (hi : x i = m)
    (h : ∀ k, x k ≤ m) : Maximum N x = m :=
  le_antisymm ((Maximum_le_iff x m).2 h) (hi ▸ le_Maximum x i)

lemma Maximum_sub_const (x : Point N) (c : ℝ) :
    Maximum N (fun i => x i - c) = Maximum N x - c := by
  obtain ⟨i, hi⟩ := exists_eq_Maximum x
  exact Maximum_eq_of _ _ i (by rw [hi]) (fun k => by linarith [le_Maximum x k])

lemma Maximum_add_diag (x : Point N) (t : ℝ) : Maximum N (x + diag t) = Maximum N x + t := by
  have := Maximum_sub_const x (-t)
  simp only [sub_neg_eq_add] at this
  exact this

lemma Maximum_diag (t : ℝ) : Maximum N (diag t) = t :=
  Maximum_eq_of _ _ ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ rfl (fun _ => le_rfl)

lemma Maximum_zero : Maximum N 0 = 0 := Maximum_diag 0

lemma Maximum_smul {c : ℝ} (hc : 0 < c) (x : Point N) : Maximum N (c • x) = c * Maximum N x := by
  obtain ⟨i, hi⟩ := exists_eq_Maximum x
  refine Maximum_eq_of _ _ i (by simp [hi]) (fun k => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (le_Maximum x k) hc.le

end Max

/-! ## Networks without biases -/

/-- A two-hidden-layer ReLU network without biases: first-layer rows `A j`, second-layer
weights `W k j`, output weights `d k`. -/
structure ZNet (N h₁ h₂ : ℕ) where
  A : Fin h₁ → Point N
  W : Fin h₂ → Fin h₁ → ℝ
  d : Fin h₂ → ℝ

variable {h₁ h₂ : ℕ}

/-- `x ↦ Σₖ dₖ σ(Σⱼ Wₖⱼ σ(Aⱼ·x))`. -/
noncomputable def ZNet.eval (net : ZNet N h₁ h₂) (x : Point N) : ℝ :=
  ∑ k, net.d k * relu (∑ j, net.W k j * relu (lin (net.A j) x))

/-- The same network with negated first-layer rows. -/
def ZNet.negIn (net : ZNet N h₁ h₂) : ZNet N h₁ h₂ := ⟨fun j => -net.A j, net.W, net.d⟩

lemma ZNet.negIn_eval (net : ZNet N h₁ h₂) (y : Point N) :
    net.negIn.eval y = net.eval (-y) := by
  simp only [ZNet.eval, ZNet.negIn, lin_neg_left, lin_neg_right]

lemma ZNet.eval_zero (net : ZNet N h₁ h₂) : net.eval 0 = 0 := by
  simp [ZNet.eval, lin_zero_right, relu]

/-- The weights of a network, with its biases dropped. -/
def _root_.MaxCaterpillar.Network.toZ (net : Network N h₁ h₂) : ZNet N h₁ h₂ := ⟨net.W₁, net.W₂, net.w₃⟩

/-- The network with all three bias arrays replaced by zero. -/
def _root_.MaxCaterpillar.Network.zeroBias (net : Network N h₁ h₂) : Network N h₁ h₂ :=
  ⟨net.W₁, 0, net.W₂, 0, net.w₃, 0⟩

lemma _root_.MaxCaterpillar.Network.zeroBias_hasZeroBiases (net : Network N h₁ h₂) : net.zeroBias.HasZeroBiases :=
  ⟨rfl, rfl, rfl⟩

lemma _root_.MaxCaterpillar.Network.zeroBias_eval (net : Network N h₁ h₂) (x : Point N) :
    net.zeroBias.eval x = net.toZ.eval x := by
  simp [Network.eval, Network.zeroBias, ZNet.eval, Network.toZ, lin]

/-- The network with its biases multiplied by `c`. -/
def _root_.MaxCaterpillar.Network.scaleBias (c : ℝ) (net : Network N h₁ h₂) : Network N h₁ h₂ :=
  ⟨net.W₁, c • net.b₁, net.W₂, c • net.b₂, net.w₃, c * net.b₃⟩

lemma _root_.MaxCaterpillar.Network.eval_smul (net : Network N h₁ h₂) {t : ℝ} (ht : 0 < t) (x : Point N) :
    net.eval (t • x) = t * (net.scaleBias t⁻¹).eval x := by
  have htt : t * t⁻¹ = 1 := mul_inv_cancel ht.ne'
  have h1 : ∀ j, relu ((∑ i, net.W₁ j i * (t • x) i) + net.b₁ j) =
      t * relu ((∑ i, net.W₁ j i * x i) + (t⁻¹ • net.b₁) j) := by
    intro j
    rw [← relu_mul_pos ht]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · rw [← mul_assoc, htt, one_mul]
  have h2 : ∀ k, relu ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * (t • x) i) + net.b₁ j))
      + net.b₂ k) = t * relu ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) +
        (t⁻¹ • net.b₁) j)) + (t⁻¹ • net.b₂) k) := by
    intro k
    rw [← relu_mul_pos ht]
    simp only [h1]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · rw [← mul_assoc, htt, one_mul]
  unfold Network.eval Network.scaleBias
  dsimp only
  simp only [h2, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by ring)
  · rw [← mul_assoc, htt, one_mul]

lemma _root_.MaxCaterpillar.Network.continuous_scaleBias_eval (net : Network N h₁ h₂) (x : Point N) :
    Continuous (fun c : ℝ => (net.scaleBias c).eval x) := by
  unfold Network.eval Network.scaleBias
  dsimp only
  refine Continuous.add (continuous_finset_sum _ fun k _ => ?_)
    (continuous_id.mul continuous_const)
  refine continuous_const.mul (continuous_relu.comp ?_)
  refine Continuous.add (continuous_finset_sum _ fun j _ => ?_) ?_
  · refine continuous_const.mul (continuous_relu.comp ?_)
    exact continuous_const.add (continuous_id.mul continuous_const)
  · exact continuous_id.mul continuous_const

/-- **Bias reduction** (Hertrich–Basu–Di Summa–Skutella, Prop. 2.3). If a network computes a
positively homogeneous function, then so does the network with all biases set to zero. -/
theorem _root_.MaxCaterpillar.Network.eval_zeroBias_of_posHom (net : Network N h₁ h₂) (f : Point N → ℝ)
    (hf : ∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c * f x) (h : ∀ x, net.eval x = f x) :
    ∀ x, net.zeroBias.eval x = f x := by
  intro x
  have hpos : ∀ c : ℝ, 0 < c → (net.scaleBias c).eval x = f x := by
    intro c hc
    have hci : 0 < c⁻¹ := inv_pos.2 hc
    have e1 := net.eval_smul hci x
    rw [inv_inv, h, hf _ hci] at e1
    exact (mul_left_cancel₀ hci.ne' e1).symm
  have hclosed : IsClosed {c : ℝ | (net.scaleBias c).eval x = f x} :=
    isClosed_eq (net.continuous_scaleBias_eval x) continuous_const
  have hsub : Set.Ioi (0 : ℝ) ⊆ {c : ℝ | (net.scaleBias c).eval x = f x} :=
    fun c hc => hpos c hc
  have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]; exact Set.left_mem_Ici
  have := hclosed.closure_subset_iff.2 hsub h0
  have he : net.scaleBias 0 = net.zeroBias := by
    simp [Network.scaleBias, Network.zeroBias]
  simp only [Set.mem_setOf_eq, he] at this
  exact this

/-- A network computing the maximum computes it after dropping all biases. -/
theorem _root_.MaxCaterpillar.Network.toZ_eval_of_max [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : ∀ x, net.toZ.eval x = Maximum N x := by
  intro x
  rw [← net.zeroBias_eval]
  exact net.eval_zeroBias_of_posHom _ (fun c hc y => Maximum_smul hc y) h x

/-! ## Odd linearity, globally and locally -/

/-- The odd part `f x - f (-x)` is a linear form. -/
def OddLin (f : Point N → ℝ) : Prop := ∃ c : Point N, ∀ x, f x - f (-x) = lin c x

/-- `f` is affine along every ray from `q`, for small positive steps. -/
def LocAff (f : Point N → ℝ) (q : Point N) : Prop :=
  ∃ c : Point N, ∀ v, ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (q + ε • v) = f q + ε * lin c v

/-- The local odd part `f (q + εv) - f (q - εv)` is linear in `v` for small `ε > 0`. -/
def LocOddLin (f : Point N → ℝ) (q : Point N) : Prop :=
  ∃ c : Point N, ∀ v, ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (q + ε • v) - f (q - ε • v) = ε * lin c v

section Odd

lemma oddLin_lin (a : Point N) : OddLin (lin a) :=
  ⟨(2 : ℝ) • a, fun x => by rw [lin_neg_right, lin_smul_left]; ring⟩

lemma oddLin_relu_lin (a : Point N) : OddLin (fun x => relu (lin a x)) :=
  ⟨a, fun x => by show relu (lin a x) - relu (lin a (-x)) = _; rw [lin_neg_right, relu_sub_relu_neg]⟩

lemma oddLin_zero : OddLin (fun _ : Point N => (0 : ℝ)) :=
  ⟨0, fun x => by rw [lin_zero_left]; ring⟩

lemma OddLin.add {f g : Point N → ℝ} (hf : OddLin f) (hg : OddLin g) :
    OddLin (fun x => f x + g x) := by
  obtain ⟨c, hc⟩ := hf; obtain ⟨c', hc'⟩ := hg
  exact ⟨c + c', fun x => by rw [lin_add_left, ← hc, ← hc']; ring⟩

lemma OddLin.const_mul {f : Point N → ℝ} (hf : OddLin f) (a : ℝ) :
    OddLin (fun x => a * f x) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨a • c, fun x => by rw [lin_smul_left, ← hc]; ring⟩

lemma OddLin.sum {ι : Type*} (s : Finset ι) {f : ι → Point N → ℝ}
    (hf : ∀ i ∈ s, OddLin (f i)) : OddLin (fun x => ∑ i in s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (oddLin_zero (N := N))
  | insert hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf _ (Finset.mem_insert_self _ _)).add
      (ih (fun i h => hf i (Finset.mem_insert_of_mem h)))

lemma OddLin.congr {f g : Point N → ℝ} (hf : OddLin f) (h : ∀ x, f x = g x) : OddLin g := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun x => by rw [← h, ← h]; exact hc x⟩

lemma OddLin.locOddLin {f : Point N → ℝ} (hf : OddLin f) : LocOddLin f 0 := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun v => Filter.eventually_of_forall fun ε => ?_⟩
  rw [zero_add, zero_sub, hc, lin_smul_right]

lemma locAff_const (a : ℝ) (q : Point N) : LocAff (fun _ => a) q :=
  ⟨0, fun v => Filter.eventually_of_forall fun ε => by rw [lin_zero_left]; ring⟩

lemma locAff_lin (a q : Point N) : LocAff (lin a) q :=
  ⟨a, fun v => Filter.eventually_of_forall fun ε => by rw [lin_add_right, lin_smul_right]⟩

lemma LocAff.add {f g : Point N → ℝ} {q : Point N} (hf : LocAff f q) (hg : LocAff g q) :
    LocAff (fun x => f x + g x) q := by
  obtain ⟨c, hc⟩ := hf; obtain ⟨c', hc'⟩ := hg
  refine ⟨c + c', fun v => ?_⟩
  filter_upwards [hc v, hc' v] with ε h1 h2
  rw [h1, h2, lin_add_left]; ring

lemma LocAff.const_mul {f : Point N → ℝ} {q : Point N} (hf : LocAff f q) (a : ℝ) :
    LocAff (fun x => a * f x) q := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨a • c, fun v => ?_⟩
  filter_upwards [hc v] with ε h1
  rw [h1, lin_smul_left]; ring

lemma LocAff.sum {ι : Type*} (s : Finset ι) {f : ι → Point N → ℝ} {q : Point N}
    (hf : ∀ i ∈ s, LocAff (f i) q) : LocAff (fun x => ∑ i in s, f i x) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locAff_const (0 : ℝ) q
  | insert hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf _ (Finset.mem_insert_self _ _)).add
      (ih (fun i h => hf i (Finset.mem_insert_of_mem h)))

lemma LocAff.congr {f g : Point N → ℝ} {q : Point N} (hf : LocAff f q) (h : ∀ x, f x = g x) :
    LocAff g q := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun v => by simpa only [h] using hc v⟩

lemma eventually_small (b : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), |ε * b| < β := by
  have ht : Tendsto (fun ε : ℝ => |ε * b|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => |ε * b|) := (continuous_id.mul continuous_const).abs
    simpa using hc.tendsto (0 : ℝ)
  exact (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hβ)

lemma LocAff.reluComp {f : Point N → ℝ} {q : Point N} (hf : LocAff f q) (h0 : f q ≠ 0) :
    LocAff (fun x => relu (f x)) q := by
  obtain ⟨c, hc⟩ := hf
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · refine ⟨0, fun v => ?_⟩
    filter_upwards [hc v, eventually_small (lin c v) (neg_pos.2 hneg)] with ε h1 h2
    rw [h1, relu_of_nonpos (by linarith [(abs_lt.1 h2).2]),
      relu_of_nonpos hneg.le, lin_zero_left]; ring
  · refine ⟨c, fun v => ?_⟩
    filter_upwards [hc v, eventually_small (lin c v) hpos] with ε h1 h2
    rw [h1, relu_of_nonneg (by linarith [(abs_lt.1 h2).1]),
      relu_of_nonneg hpos.le]

lemma LocAff.locOddLin {f : Point N → ℝ} {q : Point N} (hf : LocAff f q) : LocOddLin f q := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨(2 : ℝ) • c, fun v => ?_⟩
  filter_upwards [hc v, hc (-v)] with ε h1 h2
  have : q - ε • v = q + ε • (-v) := by rw [smul_neg, sub_eq_add_neg]
  rw [this, h1, h2, lin_neg_right, lin_smul_left]; ring

lemma LocAff.relu_locOddLin {f : Point N → ℝ} {q : Point N} (hf : LocAff f q) :
    LocOddLin (fun x => relu (f x)) q := by
  by_cases h0 : f q = 0
  · obtain ⟨c, hc⟩ := hf
    refine ⟨c, fun v => ?_⟩
    filter_upwards [hc v, hc (-v)] with ε h1 h2
    have : q - ε • v = q + ε • (-v) := by rw [smul_neg, sub_eq_add_neg]
    rw [this, h1, h2, h0, lin_neg_right, zero_add, zero_add, mul_neg, relu_sub_relu_neg]
  · exact (hf.reluComp h0).locOddLin

lemma locOddLin_const (a : ℝ) (q : Point N) : LocOddLin (fun _ => a) q :=
  (locAff_const a q).locOddLin

lemma LocOddLin.add {f g : Point N → ℝ} {q : Point N} (hf : LocOddLin f q)
    (hg : LocOddLin g q) : LocOddLin (fun x => f x + g x) q := by
  obtain ⟨c, hc⟩ := hf; obtain ⟨c', hc'⟩ := hg
  refine ⟨c + c', fun v => ?_⟩
  filter_upwards [hc v, hc' v] with ε h1 h2
  rw [lin_add_left]; linear_combination h1 + h2

lemma LocOddLin.const_mul {f : Point N → ℝ} {q : Point N} (hf : LocOddLin f q) (a : ℝ) :
    LocOddLin (fun x => a * f x) q := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨a • c, fun v => ?_⟩
  filter_upwards [hc v] with ε h1
  rw [lin_smul_left]; linear_combination a * h1

lemma LocOddLin.sum {ι : Type*} (s : Finset ι) {f : ι → Point N → ℝ} {q : Point N}
    (hf : ∀ i ∈ s, LocOddLin (f i) q) : LocOddLin (fun x => ∑ i in s, f i x) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locOddLin_const (0 : ℝ) q
  | insert hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf _ (Finset.mem_insert_self _ _)).add
      (ih (fun i h => hf i (Finset.mem_insert_of_mem h)))

lemma LocOddLin.congr {f g : Point N → ℝ} {q : Point N} (hf : LocOddLin f q)
    (h : ∀ x, f x = g x) : LocOddLin g q := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun v => by simpa only [h] using hc v⟩

end Odd

/-! ## The maximum is not locally odd-linear where three coordinates tie at the top -/

lemma unitVec_apply (i k : Fin N) : unitVec i k = if k = i then 1 else 0 := rfl

theorem not_locOddLin_max [NeZero N] (q : Point N) (I : Finset (Fin N)) (hI : 3 ≤ I.card)
    (hq0 : ∀ i ∈ I, q i = 0) (hq1 : ∀ i ∉ I, q i ≤ -1) : ¬ LocOddLin (Maximum N) q := by
  rintro ⟨c, hc⟩
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ i, Maximum N (q + ε • unitVec i) - Maximum N (q - ε • unitVec i) =
        ε * lin c (unitVec i)) ∧
      (Maximum N (q + ε • diag 1) - Maximum N (q - ε • diag 1) = ε * lin c (diag 1)) ∧
      ε ∈ Set.Ioo (0 : ℝ) 1 :=
    (Filter.eventually_all.2 fun i => hc (unitVec i)).and
      ((hc (diag 1)).and (Ioo_mem_nhdsWithin_Ioi (by norm_num)))
  obtain ⟨ε, hu, hd, hε0, hε1⟩ := hall.exists
  have hne : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨j0, hj0⟩ := hne
  -- coordinates of the shifted points
  have hci : ∀ i, c i = if i ∈ I then 1 else 0 := by
    intro i
    have h := hu i
    rw [lin_unitVec] at h
    by_cases hiI : i ∈ I
    · obtain ⟨j, hjI, hji⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < I.card) i
      have e1 : Maximum N (q + ε • unitVec i) = ε := by
        refine Maximum_eq_of _ _ i (by simp [unitVec, hq0 i hiI]) (fun k => ?_)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_apply]
        by_cases hk : k ∈ I
        · split_ifs <;> simp [hq0 k hk, hε0.le]
        · split_ifs with h' <;> [exact absurd (h' ▸ hiI) hk; linarith [hq1 k hk]]
      have e2 : Maximum N (q - ε • unitVec i) = 0 := by
        refine Maximum_eq_of _ _ j (by simp [unitVec, hq0 j hjI, hji]) (fun k => ?_)
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVec_apply]
        by_cases hk : k ∈ I
        · split_ifs <;> simp [hq0 k hk, hε0.le]
        · split_ifs <;> linarith [hq1 k hk]
      rw [e1, e2] at h; rw [if_pos hiI]
      have : ε * (c i - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1 <;> [linarith; linarith]
    · have e1 : Maximum N (q + ε • unitVec i) = 0 := by
        refine Maximum_eq_of _ _ j0 ?_ (fun k => ?_)
        · have : j0 ≠ i := fun h => hiI (h ▸ hj0)
          simp [unitVec, hq0 j0 hj0, this]
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_apply]
          by_cases hk : k ∈ I
          · split_ifs with h' <;> [exact absurd (h' ▸ hk) hiI; simp [hq0 k hk]]
          · split_ifs <;> linarith [hq1 k hk]
      have e2 : Maximum N (q - ε • unitVec i) = 0 := by
        refine Maximum_eq_of _ _ j0 ?_ (fun k => ?_)
        · have : j0 ≠ i := fun h => hiI (h ▸ hj0)
          simp [unitVec, hq0 j0 hj0, this]
        · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVec_apply]
          by_cases hk : k ∈ I
          · split_ifs <;> simp [hq0 k hk, hε0.le]
          · split_ifs <;> linarith [hq1 k hk]
      rw [e1, e2] at h; rw [if_neg hiI]
      have : ε * c i = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1 <;> [linarith; exact h1]
  have e1 : Maximum N (q + ε • diag 1) = ε := by
    refine Maximum_eq_of _ _ j0 (by simp [diag, hq0 j0 hj0]) (fun k => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, diag, mul_one]
    by_cases hk : k ∈ I
    · simp [hq0 k hk]
    · linarith [hq1 k hk]
  have e2 : Maximum N (q - ε • diag 1) = -ε := by
    refine Maximum_eq_of _ _ j0 (by simp [diag, hq0 j0 hj0]) (fun k => ?_)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diag, mul_one]
    by_cases hk : k ∈ I
    · simp [hq0 k hk]
    · linarith [hq1 k hk]
  rw [e1, e2, lin_diag, one_mul] at hd
  have hsum : ∑ i, c i = (I.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hci i), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum] at hd
  have : ε * (I.card - 2) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · have : (3 : ℝ) ≤ I.card := by exact_mod_cast hI
    linarith

/-- **Lemma 0′.** For `N ≥ 3` the odd part `max x + min x` of the maximum is not linear. -/
theorem not_oddLin_max [NeZero N] (hN : 3 ≤ N) : ¬ OddLin (Maximum N) := fun h =>
  not_locOddLin_max 0 Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]; exact hN)
    (fun _ _ => rfl) (fun i hi => absurd (Finset.mem_univ i) hi) h.locOddLin

end Frontier
end MaxCaterpillar
