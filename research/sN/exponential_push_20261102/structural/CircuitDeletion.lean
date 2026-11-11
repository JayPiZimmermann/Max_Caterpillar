import MaxCaterpillar.Frontier.StarCertificate.Anova

/-! Research-only, exact finite circuit deletion. No new axioms or computation. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush
open BigOperators
open Frontier.StarCertificate

variable {ι : Type*} [DecidableEq ι]

/-- A zero summand makes the full finite alternating difference vanish,
for an arbitrary scalar outer function. -/
theorem alternating_zero_coordinate (S : Finset ι) (u : ι → ℝ)
    (a : ℝ) (F : ℝ → ℝ) (i : ι) (hi : i ∈ S) (hu : u i = 0) :
    anchoredDifference S (fun T => F (a + ∑ j in T, u j)) = 0 := by
  rw [← Finset.insert_erase hi]
  rw [anchoredDifference_insert _ i (Finset.not_mem_erase i S)]
  unfold anchoredDifference
  apply Finset.sum_eq_zero
  intro T hT
  have hiT : i ∉ T := fun h => (Finset.not_mem_erase i S)
    ((Finset.mem_powerset.mp hT) h)
  dsimp only
  rw [Finset.sum_insert hiT, hu, zero_add, sub_self, mul_zero]

/-- The full neuron is a signed sum of neurons omitting at least one term.
The coefficients in the sum are all plus or minus one. -/
theorem proper_subset_deletion (S : Finset ι) (u : ι → ℝ)
    (a : ℝ) (F : ℝ → ℝ) (i : ι) (hi : i ∈ S) (hu : u i = 0) :
    F (a + ∑ j in S, u j) =
      - ∑ T in S.powerset.erase S,
        (-1 : ℝ) ^ (S \ T).card * F (a + ∑ j in T, u j) := by
  have hz := alternating_zero_coordinate S u a F i hi hu
  unfold anchoredDifference at hz
  have he := Finset.sum_erase_add S.powerset
    (fun T => (-1 : ℝ) ^ (S \ T).card * F (a + ∑ j in T, u j))
    (Finset.mem_powerset_self S)
  simp only [Finset.sdiff_self, Finset.card_empty, pow_zero, one_mul] at he
  linarith

/-- A nonempty positive circuit has a zero ReLU in every real evaluation. -/
theorem positive_circuit_zero_hinge (S : Finset ι) (ell : ι → ℝ)
    (hS : S.Nonempty) (hzero : ∑ i in S, ell i = 0) :
    ∃ i ∈ S, max (ell i) 0 = 0 := by
  have hex : ∃ i ∈ S, ell i ≤ 0 := by
    by_contra! hall
    have hp : 0 < ∑ i in S, ell i := Finset.sum_pos hall hS
    linarith
  obtain ⟨i, hi, he⟩ := hex
  exact ⟨i, hi, max_eq_right he⟩

/-- All-real circuit deletion, with arbitrary signed weights and arbitrary
outer function. In a graph, orient a cycle cyclically to obtain hzero. -/
theorem circuit_deletion (S : Finset ι) (ell c : ι → ℝ)
    (a : ℝ) (F : ℝ → ℝ) (hS : S.Nonempty)
    (hzero : ∑ i in S, ell i = 0) :
    F (a + ∑ i in S, c i * max (ell i) 0) =
      - ∑ T in S.powerset.erase S, (-1 : ℝ) ^ (S \ T).card *
        F (a + ∑ i in T, c i * max (ell i) 0) := by
  obtain ⟨i, hi, hz⟩ := positive_circuit_zero_hinge S ell hS hzero
  exact proper_subset_deletion S (fun j => c j * max (ell j) 0)
    a F i hi (by dsimp only; rw [hz, mul_zero])

#print axioms alternating_zero_coordinate
#print axioms proper_subset_deletion
#print axioms positive_circuit_zero_hinge
#print axioms circuit_deletion
end MaxCaterpillar.ExponentialPush
