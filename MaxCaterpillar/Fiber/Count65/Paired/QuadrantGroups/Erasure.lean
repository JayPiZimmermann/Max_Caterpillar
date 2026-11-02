import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.ClusterPath

/-! # Erase a cancelling finite physical readout group

Cancellation is a local group identity, not a hypothesis of global attachment.
The actual path changes only the selected output coefficients; all incoming
parameters, biases, and spectator outputs remain fixed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators Absorption

noncomputable def eraseClusterOutput {k : ℕ} (d : Fin k → ℝ)
    (s : Finset (Fin k)) : Fin k → ℝ := fun i => if i ∈ s then 0 else d i

theorem eraseClusterOutput_sum {k : ℕ} (d f : Fin k → ℝ)
    (s : Finset (Fin k)) (hzero : (∑ i in s, d i*f i) = 0) :
    (∑ i, eraseClusterOutput d s i*f i) = ∑ i, d i*f i := by
  classical
  have hfilter : Finset.univ.filter (fun i => i ∈ s) = s := by
    ext i
    simp
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (fun i => i ∈ s) (fun i => d i*f i)
  rw [hfilter,hzero,zero_add] at hpartition
  rw [← hpartition,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : i ∈ s <;> simp [eraseClusterOutput,hi]

theorem eraseCancelingCluster_eval {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k))
    (hzero : ∀ x, (∑ i in s, net.w₃ i*
      relu (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) = 0) (x : Point N) :
    (withOutput net (eraseClusterOutput net.w₃ s) net.b₃).eval x = net.eval x := by
  unfold withOutput Network.eval
  congr 1
  exact eraseClusterOutput_sum net.w₃ _ s (hzero x)

theorem eraseCancelingCluster_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (s : Finset (Fin k))
    (hzero : ∀ x, (∑ i in s, net.val.w₃ i*
      relu (preact net.val.W₁ net.val.b₁ (net.val.W₂ i) (net.val.b₂ i) x)) = 0) :
    JoinedIn (ExactSet N m k) net.val
      (withOutput net.val (eraseClusterOutput net.val.w₃ s) net.val.b₃) := by
  apply JoinedIn.ofLine
    (continuous_interpolateOutput net.val
      (eraseClusterOutput net.val.w₃ s) net.val.b₃).continuousOn
    (interpolateOutput_zero _ _ _) (interpolateOutput_one _ _ _)
  rintro _ ⟨t,_ht,rfl⟩ x
  rw [interpolateOutput_eval,eraseCancelingCluster_eval net.val s hzero x,net.property x]
  ring

theorem eraseCluster_interpolation_spectator {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (i : Fin k) (hi : i ∉ s) (t : ℝ) :
    (interpolateOutput net (eraseClusterOutput net.w₃ s) net.b₃ t).w₃ i = net.w₃ i := by
  simp only [interpolateOutput,withOutput,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    eraseClusterOutput,if_neg hi]
  ring

/-- An actual zero-coefficient knot group is erasable. Its cancellation is
derived from the exact quadrant identity and the physical feature bridge. -/
theorem eraseZeroKnotGroup_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (a b : Fin k → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, net.val.w₃ i*max 0 (a i*Q+b i*N)) = Q-N)
    (hP : groupCoefficient a b net.val.w₃ τ = 0) (Q R : Point N → ℝ)
    (hpre : ∀ i ∈ knotGroup a b τ, ∀ x,
      preact net.val.W₁ net.val.b₁ (net.val.W₂ i) (net.val.b₂ i) x =
        a i*Q x+b i*R x) :
    JoinedIn (ExactSet N m k) net.val
      (withOutput net.val (eraseClusterOutput net.val.w₃ (knotGroup a b τ)) net.val.b₃) := by
  apply eraseCancelingCluster_joinedIn_exact
  intro x
  calc
    _ = ∑ i in knotGroup a b τ, net.val.w₃ i*max 0 (a i*Q x+b i*R x) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpre i hi x]
      rfl
    _ = 0 := knotGroup_zero_cancels a b net.val.w₃ τ hτ hfit hP (Q x) (R x)

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
