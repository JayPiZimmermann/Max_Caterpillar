import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Collapse an arbitrary finite proportional cluster in physical parameters

A single output interpolation merges the cluster into a chosen existing slot.
Incoming parameters, all biases, and every output outside the cluster remain
fixed. The core theorem assumes functional proportionality of preactivations,
so redundant first features and arbitrary signed output weights are allowed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators Absorption

/-- Merge the selected readout coefficients, retaining all spectators. -/
noncomputable def mergeClusterOutput {k : ℕ} (d : Fin k → ℝ)
    (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ) : Fin k → ℝ :=
  fun i => (if i ∈ s then 0 else d i)+
    (if i=p then ∑ j in s, d j*c j else 0)

theorem mergeClusterOutput_rep {k : ℕ} (d : Fin k → ℝ)
    (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ) (hp : p ∈ s) :
    mergeClusterOutput d s p c p = ∑ j in s, d j*c j := by
  simp [mergeClusterOutput,hp]

theorem mergeClusterOutput_removed {k : ℕ} (d : Fin k → ℝ)
    (s : Finset (Fin k)) (p i : Fin k) (c : Fin k → ℝ)
    (hi : i ∈ s) (hip : i ≠ p) :
    mergeClusterOutput d s p c i = 0 := by
  simp [mergeClusterOutput,hi,hip]

theorem mergeClusterOutput_spectator {k : ℕ} (d : Fin k → ℝ)
    (s : Finset (Fin k)) (p i : Fin k) (c : Fin k → ℝ)
    (hp : p ∈ s) (hi : i ∉ s) :
    mergeClusterOutput d s p c i = d i := by
  have hip : i ≠ p := by rintro rfl; exact hi hp
  simp [mergeClusterOutput,hi,hip]

theorem mergeClusterOutput_sum {k : ℕ} (d f c : Fin k → ℝ)
    (s : Finset (Fin k)) (p : Fin k)
    (hf : ∀ i ∈ s, f i = c i*f p) :
    (∑ i, mergeClusterOutput d s p c i*f i) = ∑ i, d i*f i := by
  classical
  have hgroup : (∑ i in s, d i*c i)*f p = ∑ i in s, d i*f i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hf i hi]
    ring
  have hout : (∑ i, (if i ∈ s then 0 else d i)*f i) =
      ∑ i in Finset.univ.filter (fun i => i ∉ s), d i*f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i ∈ s <;> simp [hi]
  have hfilter : Finset.univ.filter (fun i => i ∈ s) = s := by
    ext i
    simp
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (fun i => i ∈ s) (fun i => d i*f i)
  rw [hfilter] at hpartition
  unfold mergeClusterOutput
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [ite_mul,zero_mul] at hout
  rw [hout,hgroup,add_comm]
  exact hpartition

/-- Functional proportionality is sufficient for the physical output merge. -/
theorem mergeCluster_eval {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hpre : ∀ i ∈ s, ∀ x,
      preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x =
        c i*preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x) (x : Point N) :
    (withOutput net (mergeClusterOutput net.w₃ s p c) net.b₃).eval x = net.eval x := by
  unfold withOutput Network.eval
  congr 1
  apply mergeClusterOutput_sum
  intro i hi
  change relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x) =
    c i*relu (preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x)
  rw [hpre i hi x]
  change max 0 (c i*_) = c i*max 0 _
  rw [mul_max_of_nonneg _ _ (hc i hi),mul_zero]

/-- Every intermediate physical readout retains all spectator weights. -/
theorem mergeCluster_interpolation_spectator {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p i : Fin k) (c : Fin k → ℝ)
    (hp : p ∈ s) (hi : i ∉ s) (t : ℝ) :
    (interpolateOutput net (mergeClusterOutput net.w₃ s p c) net.b₃ t).w₃ i =
      net.w₃ i := by
  simp only [interpolateOutput,withOutput,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [mergeClusterOutput_spectator net.w₃ s p i c hp hi]
  ring

/-- Both hidden affine layers and all biases are fixed along the whole path. -/
theorem mergeCluster_interpolation_fixed {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ) (t : ℝ) :
    let moved := interpolateOutput net (mergeClusterOutput net.w₃ s p c) net.b₃ t
    moved.W₁ = net.W₁ ∧ moved.b₁ = net.b₁ ∧ moved.W₂ = net.W₂ ∧
      moved.b₂ = net.b₂ ∧ moved.b₃ = net.b₃ := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  change (1-t)*net.b₃+t*net.b₃ = net.b₃
  ring

noncomputable def mergeClusterPath {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hpre : ∀ i ∈ s, ∀ x,
      preact net.val.W₁ net.val.b₁ (net.val.W₂ i) (net.val.b₂ i) x =
        c i*preact net.val.W₁ net.val.b₁ (net.val.W₂ p) (net.val.b₂ p) x) :
    Path net (⟨withOutput net.val (mergeClusterOutput net.val.w₃ s p c) net.val.b₃,
      fun x => (mergeCluster_eval net.val s p c hc hpre x).trans
        (net.property x)⟩ : ExactFiber N m k) :=
  outputInterpolationPath net (mergeClusterOutput net.val.w₃ s p c) net.val.b₃
    (fun x => (mergeCluster_eval net.val s p c hc hpre x).trans (net.property x))

/-- Ambient joinedness of the actual parameter endpoints in the exact set. -/
theorem mergeCluster_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hpre : ∀ i ∈ s, ∀ x,
      preact net.val.W₁ net.val.b₁ (net.val.W₂ i) (net.val.b₂ i) x =
        c i*preact net.val.W₁ net.val.b₁ (net.val.W₂ p) (net.val.b₂ p) x) :
    JoinedIn (ExactSet N m k) net.val
      (withOutput net.val (mergeClusterOutput net.val.w₃ s p c) net.val.b₃) := by
  apply JoinedIn.ofLine
    (continuous_interpolateOutput net.val
      (mergeClusterOutput net.val.w₃ s p c) net.val.b₃).continuousOn
    (interpolateOutput_zero _ _ _) (interpolateOutput_one _ _ _)
  rintro _ ⟨t,_ht,rfl⟩ x
  rw [interpolateOutput_eval,mergeCluster_eval net.val s p c hc hpre x,net.property x]
  ring

/-- Coefficientwise proportional rows and biases imply the functional
hypothesis, with arbitrary first-layer features and biases. -/
theorem proportional_rows_preact {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ)
    (hrow : ∀ i ∈ s, ∀ l, net.W₂ i l = c i*net.W₂ p l)
    (hbias : ∀ i ∈ s, net.b₂ i = c i*net.b₂ p) :
    ∀ i ∈ s, ∀ x,
      preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x =
        c i*preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x := by
  intro i hi x
  simp only [preact,hrow i hi,hbias i hi,mul_assoc,← Finset.mul_sum]
  ring

theorem mergeProportionalCluster_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (s : Finset (Fin k)) (p : Fin k) (c : Fin k → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hrow : ∀ i ∈ s, ∀ l, net.val.W₂ i l = c i*net.val.W₂ p l)
    (hbias : ∀ i ∈ s, net.val.b₂ i = c i*net.val.b₂ p) :
    JoinedIn (ExactSet N m k) net.val
      (withOutput net.val (mergeClusterOutput net.val.w₃ s p c) net.val.b₃) :=
  mergeCluster_joinedIn_exact net s p c hc
    (proportional_rows_preact net.val s p c hrow hbias)

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
