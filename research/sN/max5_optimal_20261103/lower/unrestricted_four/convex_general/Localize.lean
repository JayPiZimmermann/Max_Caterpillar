import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Tangent
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.ConvexTangent
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.ContactMaximum

/-! An actual signed-fold identity loses a core when that core is nonzero
at a top tie. All affine biases, arbitrary directions and zero plateaus remain. -/

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Filter Topology Frontier
open Frontier.RandomRestriction.NormalizedNetwork

variable {N m : ℕ} [NeZero N] [NeZero m]

private lemma pick_split (a b : ℝ) :
    pick a b (relu b) = (if 0 < a then b else 0) +
      (if a = 0 then relu b else 0) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · simp [pick, ha, not_lt.mpr ha.le, ha.ne]
  · simp [pick, ha]
  · simp [pick, ha, ha.ne']

private lemma sum_subtype_ne {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : κ → ℝ) (k : κ) (hk : F k = 0) :
    (∑ j : {j : κ // j ≠ k}, F j) = ∑ j, F j := by
  rw [← Finset.sum_subtype (Finset.univ.erase k) (fun j => by simp) F]
  simpa [hk] using Finset.sum_erase_add Finset.univ F (Finset.mem_univ k)

/-- Exact differentiation of the full signed expression at an arbitrary top tie. -/
theorem folded_tangent_identity {κ : Type*} [Fintype κ]
    (R : Point N → ℝ) (g : κ → Point N → ℝ) (d : κ → ℝ)
    (DR : Point m → ℝ) (D : κ → Point m → ℝ)
    (q : Point N) (e : Fin m ↪ Fin N) (M : ℝ)
    (hq : ∀ a, q (e a) = M)
    (hbelow : ∀ i, i ∉ Finset.univ.image e → q i < M)
    (hR : ExactTangent R q e DR) (hg : ∀ j, ExactTangent (g j) q e (D j))
    (heq : ∀ x, R x + ∑ j, d j * relu (g j x) = Maximum N x) :
    ∀ x, DR x + ∑ j, d j * pick (g j q) (D j x) (relu (D j x)) = Maximum m x := by
  intro x
  have htotal := hR.add (ExactTangent.sum
    (fun j y => d j * relu (g j y))
    (fun j y => d j * pick (g j q) (D j y) (relu (D j y)))
    (fun j => (hg j).relu.smul (d j)))
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hd, ht⟩ :=
    (hp.and ((htotal x).and
      (eventually_tied_Maximum_at_level e q M hq hbelow x))).exists
  change R (q + ε • lift e x) + ∑ j, d j * relu (g j (q + ε • lift e x)) =
    (R q + ∑ j, d j * relu (g j q)) +
      ε * (DR x + ∑ j, d j * pick (g j q) (D j x) (relu (D j x))) at hd
  rw [heq, heq, tied_Maximum_eq_level e q M hq hbelow, ht] at hd
  exact mul_left_cancel₀ hε.ne' ((add_left_cancel hd).symm)

/-- Removing a chosen nonzero core is an actual representation reduction,
not a conditional counting assumption. -/
theorem ConvexRepresentation.localize {κ : Type*} [Fintype κ] [DecidableEq κ]
    (net : ConvexRepresentation N κ) (e : Fin m ↪ Fin N) (q : Point N) (M : ℝ)
    (hq : ∀ a, q (e a) = M)
    (hbelow : ∀ i, i ∉ Finset.univ.image e → q i < M)
    (k : κ) (hk : net.core k q ≠ 0) :
    Nonempty (ConvexRepresentation m {j : κ // j ≠ k}) := by
  classical
  obtain ⟨DR, hDR, htR⟩ := net.shallow_remainder.exists_tangent q e
  have hex : ∀ j, ∃ D : Point m → ℝ, IsShallow D ∧ ExactTangent (net.core j) q e D :=
    fun j => (net.shallow_core j).exists_tangent q e
  choose D hD htD using hex
  let R' : Point m → ℝ := fun x => DR x + ∑ j,
    net.weight j * (if 0 < net.core j q then D j x else 0)
  let d' : {j : κ // j ≠ k} → ℝ := fun j =>
    if net.core j q = 0 then net.weight j else 0
  refine ⟨{
    remainder := R'
    core := fun j => D j
    weight := d'
    shallow_remainder := ?_
    shallow_core := fun j => hD j
    convex_core := fun j => (htD j).convex (net.convex_core j)
    computes := ?_ }⟩
  · apply hDR.add
    apply IsShallow.sum Finset.univ
    intro j _
    by_cases hj : 0 < net.core j q
    · simpa only [if_pos hj] using IsShallow.smul (net.weight j) (hD j)
    · simpa only [if_neg hj, mul_zero] using (IsShallow.zero (N := m))
  · intro x
    have hid := folded_tangent_identity net.remainder net.core net.weight DR D q e M
      hq hbelow htR htD net.computes x
    have hdrop :
        (∑ j : {j : κ // j ≠ k},
          (if net.core j q = 0 then net.weight j else 0) * relu (D j x)) =
        ∑ j, (if net.core j q = 0 then net.weight j else 0) * relu (D j x) :=
      sum_subtype_ne
        (fun j : κ => (if net.core j q = 0 then net.weight j else 0) * relu (D j x))
        k (by
          change (if net.core k q = 0 then net.weight k else 0) * relu (D k x) = 0
          rw [if_neg hk, zero_mul])
    change R' x + ∑ j, d' j * relu (D j x) = Maximum m x
    dsimp only [R', d']
    rw [hdrop, add_assoc, ← Finset.sum_add_distrib]
    convert hid using 2
    apply Finset.sum_congr rfl
    intro j _
    rw [pick_split]
    split_ifs <;> ring

#check @folded_tangent_identity
#print axioms folded_tangent_identity
#check @ConvexRepresentation.localize
#print axioms ConvexRepresentation.localize
end MaxCaterpillar.Max5Optimal.ConvexCores
