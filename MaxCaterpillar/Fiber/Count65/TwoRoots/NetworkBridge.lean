import MaxCaterpillar.Fiber.Count65.InvariantReduction
import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Fiber.Count65.TwoRoots.Outward

/-! # From actual six-row first matrices to normalized four-feature obstructions -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier BigOperators

/-- Relabeling the input coordinates preserves the normalized representation. -/
theorem Represents.permute {A : Fin 4 → Point 4} (h : Represents A)
    (q : Equiv.Perm (Fin 4)) : Represents (fun j i => A j (q i)) := by
  obtain ⟨ell,Phi,h⟩ := h
  refine ⟨fun i => ell (q i),Phi,fun x => ?_⟩
  have hlin (a : Point 4) : lin (fun i => a (q i)) x =
      lin a (fun i => x (q.symm i)) := by
    exact Fintype.sum_equiv q _ _ (fun i => by
      change a (q i) * x i = a (q i) * x (q.symm (q i))
      rw [q.symm_apply_apply])
  rw [hlin ell]
  have hstate : (fun j => relu (lin (fun i => A j (q i)) x)) =
      (fun j => relu (lin (A j) (fun i => x (q.symm i)))) := by
    funext j
    rw [hlin]
  rw [hstate]
  exact (maximum_permute q.symm x).symm.trans (h (fun i => x (q.symm i)))

/-- A column permutation in a displayed first matrix can be removed before
applying the normalized branch exclusions. -/
theorem Represents.unpermute {A : Fin 4 → Point 4} (q : Equiv.Perm (Fin 4))
    (h : Represents (fun j i => A j (q i))) : Represents A := by
  have hp := h.permute q.symm
  simpa only [q.apply_symm_apply] using hp

/-- Positive rescaling and reindexing of the four invariant rows preserve
an arbitrary-decoder representation. The carrier rows are unconstrained. -/
theorem network_represents_of_invariant_rows (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (A : Fin 4 → Point 4) (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ)
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 → net.W₁ j = s j • A (p j)) :
    Represents A := by
  classical
  obtain ⟨ell,Phi,hfactor,_,_,_⟩ := four_invariant_factorization net hnet hcard
  let lift : (Fin 4 → ℝ) → Fin 6 → ℝ := fun z j =>
    if (∑ i, net.W₁ j i) = 0 then s j * z (p j) else 0
  refine ⟨ell,fun z => Phi (lift z),fun x => ?_⟩
  have hstate : invariantState net x = lift (fun j => relu (lin (A j) x)) := by
    funext j
    change (if (∑ i, net.W₁ j i) = 0 then relu (lin (net.W₁ j) x) else 0) =
      (if (∑ i, net.W₁ j i) = 0 then s j * relu (lin (A (p j)) x) else 0)
    by_cases hj : (∑ i, net.W₁ j i) = 0
    · rw [if_pos hj,if_pos hj,hrows j hj,lin_smul_left,relu_mul_pos (hs j hj)]
    · rw [if_neg hj,if_neg hj]
  rw [hfactor x,hstate]

/-- The same actual-network bridge with arbitrary input relabeling explicit. -/
theorem network_represents_of_invariant_rows_permuted (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (A : Fin 4 → Point 4) (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ)
    (q : Equiv.Perm (Fin 4))
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • (fun i => A (p j) (q i))) : Represents A :=
  Represents.unpermute q
    (network_represents_of_invariant_rows net hnet hcard (fun j i => A j (q i)) p s hs hrows)

/-- The normalized inward fork inequality now follows from an actual
network, with arbitrary biases and every second-layer coefficient free. -/
theorem network_fork_bounds (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (α β κ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ)
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • forkRows α β κ (p j)) :
    max α β ≤ κ ∧ 0 < κ :=
  fork_facet_bounds hα hβ
    (network_represents_of_invariant_rows net hnet hcard _ p s hs hrows)

/-- No actual network can have this normalized outward two-root branch. -/
theorem network_outward_fork_excluded (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (a b c : ℝ) (t : Point 4) (hsum : a+b+c = 0) (ha : a ≠ 0)
    (ht : Nonroot t) (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ)
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • outwardRows a b c t (p j)) : False :=
  outward_fork_excluded a b c t hsum ha ht
    (network_represents_of_invariant_rows net hnet hcard _ p s hs hrows)

#print axioms network_represents_of_invariant_rows_permuted
#print axioms network_represents_of_invariant_rows
#print axioms network_fork_bounds
#print axioms network_outward_fork_excluded
end MaxCaterpillar.Fiber.Count65.TwoRoots
