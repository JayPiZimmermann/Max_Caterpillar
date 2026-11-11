import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Localize

/-! Convex shallow cores require at least N-2 outer folds for exact MAX_N.
All affine biases, signed outer weights, and separate finite shallow
dictionaries are allowed. The proof is induction on input arity. -/

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Frontier

universe u

/-- Every exact MAX representation by a shallow remainder and globally
convex shallow cores has at least N-2 cores. -/
theorem ConvexRepresentation.bound (N : ℕ) :
    ∀ [NeZero N] {κ : Type u} [Fintype κ],
      ConvexRepresentation N κ → N ≤ Fintype.card κ + 2 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro inst κ fκ net
    classical
    by_contra hn
    have hN : 3 ≤ N := by omega
    cases N with
    | zero => exact (NeZero.ne (0 : ℕ)) rfl
    | succ n =>
      have hnpos : 0 < n := by omega
      letI : NeZero n := ⟨by omega⟩
      have hz (M s : ℝ) (hs : 0 < s) (i : Fin (n+1)) (k : κ) :
          net.core k (contactVertex M s i) = 0 := by
        by_contra hk
        obtain ⟨net'⟩ := net.localize (omitEmbedding i) (contactVertex M s i) M
          (contactVertex_selected M s i)
          (fun j hj => by rw [contactVertex_outside M s i j hj]; linarith only [hs])
          k hk
        have hsmall := ih n (Nat.lt_succ_self n) net'
        have hcard : Fintype.card {j : κ // j ≠ k} < Fintype.card κ :=
          Fintype.card_subtype_lt (x := k) (by simp)
        omega
      have hnonpos (k : κ) (x : Point (n+1)) : net.core k x ≤ 0 :=
        convex_nonpos_of_contact_zeros (net.convex_core k)
          (fun M s hs i => hz M s hs i k) x
      have hsh : IsShallow (Maximum (n+1)) := net.shallow_remainder.congr (fun x => by
        have hsum : (∑ k, net.weight k * relu (net.core k x)) = 0 :=
          Finset.sum_eq_zero (fun k _ => by rw [relu_of_nonpos (hnonpos k x), mul_zero])
        simpa only [hsum, add_zero] using net.computes x)
      exact not_shallow_max hN hsh

/-- The literal function-level statement; no normalization is assumed. -/
theorem convex_core_lower_bound {N : ℕ} [NeZero N] {κ : Type u} [Fintype κ]
    (R : Point N → ℝ) (g : κ → Point N → ℝ) (d : κ → ℝ)
    (hR : IsShallow R) (hg : ∀ k, IsShallow (g k))
    (hc : ∀ k, ConvexOn ℝ Set.univ (g k))
    (heq : ∀ x, R x + ∑ k, d k * relu (g k x) = Maximum N x) :
    N ≤ Fintype.card κ + 2 :=
  ConvexRepresentation.bound N
    { remainder := R, core := g, weight := d, shallow_remainder := hR,
      shallow_core := hg, convex_core := hc, computes := heq }

#check @ConvexRepresentation.bound
#check @convex_core_lower_bound
#print axioms ConvexRepresentation.bound
#print axioms convex_core_lower_bound
end MaxCaterpillar.Max5Optimal.ConvexCores
