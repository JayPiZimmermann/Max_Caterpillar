import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Bound

/-! Complement concave cores without changing their count or outer signs.
The shallow remainder absorbs the exact linear-in-the-core correction. -/

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Frontier

theorem exists_convex_representation {N : ℕ} [NeZero N]
    {κ : Type*} [Fintype κ] (R : Point N → ℝ) (g : κ → Point N → ℝ)
    (d : κ → ℝ) (hR : IsShallow R) (hg : ∀ k, IsShallow (g k))
    (hshape : ∀ k, ConvexOn ℝ Set.univ (g k) ∨ ConcaveOn ℝ Set.univ (g k))
    (heq : ∀ x, R x + ∑ k, d k * relu (g k x) = Maximum N x) :
    Nonempty (ConvexRepresentation N κ) := by
  classical
  let G : κ → Point N → ℝ := fun k =>
    if ConvexOn ℝ Set.univ (g k) then g k else fun x => -g k x
  let correction : κ → Point N → ℝ := fun k x =>
    if ConvexOn ℝ Set.univ (g k) then 0 else d k * g k x
  have hc : ∀ k, IsShallow (correction k) := by
    intro k
    by_cases h : ConvexOn ℝ Set.univ (g k)
    · simpa only [correction, if_pos h] using (IsShallow.zero (N := N))
    · simpa only [correction, if_neg h] using IsShallow.smul (d k) (hg k)
  have hG : ∀ k, IsShallow (G k) := by
    intro k
    by_cases h : ConvexOn ℝ Set.univ (g k)
    · simpa only [G, if_pos h] using hg k
    · simpa only [G, if_neg h] using (hg k).neg
  have hconvex : ∀ k, ConvexOn ℝ Set.univ (G k) := by
    intro k
    by_cases h : ConvexOn ℝ Set.univ (g k)
    · simpa only [G, if_pos h] using h
    · simpa only [G, if_neg h, Pi.neg_apply] using ((hshape k).resolve_left h).neg
  refine ⟨{
    remainder := fun x => R x + ∑ k, correction k x
    core := G
    weight := d
    shallow_remainder := hR.add (IsShallow.sum Finset.univ correction (fun k _ => hc k))
    shallow_core := hG
    convex_core := hconvex
    computes := ?_
  }⟩
  intro x
  rw [← heq x, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : ConvexOn ℝ Set.univ (g k)
  · simp only [correction, G, if_pos h, zero_add]
  · simp only [correction, G, if_neg h]
    linear_combination -(d k) * relu_sub_relu_neg (g k x)

/-- Either curvature sign is allowed separately for each core, while
outer coefficients retain arbitrary signs and magnitudes. -/
theorem shape_bound {N : ℕ} [NeZero N] {κ : Type*} [Fintype κ]
    (R : Point N → ℝ) (g : κ → Point N → ℝ) (d : κ → ℝ)
    (hR : IsShallow R) (hg : ∀ k, IsShallow (g k))
    (hshape : ∀ k, ConvexOn ℝ Set.univ (g k) ∨ ConcaveOn ℝ Set.univ (g k))
    (heq : ∀ x, R x + ∑ k, d k * relu (g k x) = Maximum N x) :
    N ≤ Fintype.card κ + 2 := by
  obtain ⟨net⟩ := exists_convex_representation R g d hR hg hshape heq
  exact ConvexRepresentation.bound N net

/-- Literal affine arrays: all first biases, core biases, and the remainder
bias are retained. Different cores may use different finite dictionaries. -/
theorem raw_shape_bound {N K mR mg : ℕ} [NeZero N]
    (aR : Point N) (bR : ℝ) (AR : Fin mR → Point N) (βR cR : Fin mR → ℝ)
    (ag : Fin K → Point N) (bg : Fin K → ℝ)
    (Ag : Fin K → Fin mg → Point N) (βg cg : Fin K → Fin mg → ℝ)
    (d : Fin K → ℝ)
    (hshape : ∀ k,
      ConvexOn ℝ Set.univ (fun x => lin (ag k) x + bg k +
        ∑ j, cg k j * relu (lin (Ag k j) x + βg k j)) ∨
      ConcaveOn ℝ Set.univ (fun x => lin (ag k) x + bg k +
        ∑ j, cg k j * relu (lin (Ag k j) x + βg k j)))
    (heq : ∀ x, lin aR x + bR + ∑ j, cR j * relu (lin (AR j) x + βR j) +
      ∑ k, d k * relu (lin (ag k) x + bg k +
        ∑ j, cg k j * relu (lin (Ag k j) x + βg k j)) = Maximum N x) :
    N ≤ K + 2 := by
  simpa only [Fintype.card_fin] using shape_bound
    (fun x => lin aR x + bR + ∑ j, cR j * relu (lin (AR j) x + βR j))
    (fun k x => lin (ag k) x + bg k + ∑ j, cg k j * relu (lin (Ag k j) x + βg k j))
    d (IsShallow.raw aR bR AR βR cR)
    (fun k => IsShallow.raw (ag k) (bg k) (Ag k) (βg k) (cg k)) hshape heq

/-- MAX5 needs a genuinely nonconvex and nonconcave core in every
two-core shallow-remainder representation. This is not a statement that
every physical four-neuron network has a two-core reduction. -/
theorem max5_two_core_impossible
    (R : Point 5 → ℝ) (g : Fin 2 → Point 5 → ℝ) (d : Fin 2 → ℝ)
    (hR : IsShallow R) (hg : ∀ k, IsShallow (g k))
    (hshape : ∀ k, ConvexOn ℝ Set.univ (g k) ∨ ConcaveOn ℝ Set.univ (g k))
    (heq : ∀ x, R x + ∑ k, d k * relu (g k x) = Maximum 5 x) : False := by
  have h := shape_bound R g d hR hg hshape heq
  norm_num at h

#check @exists_convex_representation
#check @shape_bound
#check @raw_shape_bound
#check @max5_two_core_impossible
#print axioms exists_convex_representation
#print axioms shape_bound
#print axioms raw_shape_bound
#print axioms max5_two_core_impossible
end MaxCaterpillar.Max5Optimal.ConvexCores
