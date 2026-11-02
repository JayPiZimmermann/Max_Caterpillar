import MaxCaterpillar.Fiber.Count65.ThreeRoots.Path
import MaxCaterpillar.Fiber.Count65.ThreeRoots.Star
import MaxCaterpillar.Fiber.Count65.ThreeRoots.Triangle
import MaxCaterpillar.Fiber.Count65.ThreeRoots.Opposite
import MaxCaterpillar.Fiber.Count65.TwoRoots.NetworkBridge
import MaxCaterpillar.Fiber.Count65.Classification

/-! # Three-root geometry for actual biased Max4 networks

The only matrix premise is an explicit positive scaling and input relabeling
of the actual invariant rows. The decoder representation and coordinate-zero
coverage are conclusions of the original all-input network equation.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ThreeRoots
open MaxCaterpillar.Frontier BigOperators TwoRoots

/-- Reordering observations only reorders the inputs to the arbitrary decoder. -/
theorem _root_.MaxCaterpillar.Fiber.Count65.TwoRoots.Represents.reindex_rows {A : Fin 4 → Point 4} (h : Represents A)
    (p : Equiv.Perm (Fin 4)) : Represents (fun j => A (p j)) := by
  obtain ⟨ell,Phi,h⟩ := h
  refine ⟨ell,fun z => Phi (fun j => z (p.symm j)),fun x => ?_⟩
  simpa only [p.apply_symm_apply] using h x

private def reverseInputs : Equiv.Perm (Fin 4) where
  toFun := ![3,2,1,0]
  invFun := ![3,2,1,0]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- Reversing input labels and swapping the end observations sends the
second surviving path orientation to the first, with explicit coefficients. -/
theorem path_reverse_represents (b c : ℝ)
    (h : Represents (pathRows true false false 0 b c)) :
    Represents (pathRows true true false (-c) (-b) 0) := by
  have hh := (h.permute reverseInputs).reindex_rows (Equiv.swap 0 2)
  have he : (fun j i => pathRows true false false 0 b c
      (Equiv.swap 0 2 j) (reverseInputs i)) =
      pathRows true true false (-c) (-b) 0 := by
    funext j i
    fin_cases j <;> fin_cases i <;>
      norm_num [pathRows,pathFourth,reverseInputs,Equiv.swap_apply_def,Fin.ext_iff,
        show (3 : Fin 4).val = 3 from rfl] <;> first | rfl | ring
  rw [he] at hh
  exact hh

/-- C3 is obtained from the actual network, rather than assumed as a
classification predicate. Row reindexing need not be specified bijective. -/
theorem network_normalized_frame_cover (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (A : Fin 4 → Point 4) (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ)
    (q : Equiv.Perm (Fin 4))
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • (fun i => A (p j) (q i))) :
    ∀ i, ∃ j, A j i = 0 := by
  intro i
  obtain ⟨j,hj,hji⟩ := max4_invariant_row_at_top_tie net hnet (q.symm i)
  have he := congrFun (hrows j hj) (q.symm i)
  change net.W₁ j (q.symm i) = s j * A (p j) (q (q.symm i)) at he
  rw [q.apply_symm_apply,hji] at he
  exact ⟨p j,(mul_eq_zero.mp he.symm).resolve_left (ne_of_gt (hs j hj))⟩

/-- The canonical path's actual facet test feeds the independently defined
mixed/star/wall coefficient cases. -/
theorem canonical_path_coefficient_case (a b : ℝ)
    (h : Represents (pathRows true true false a b 0))
    (ht : Nonroot (pathFourth a b 0)) : PathCoefficientCase a b := by
  have hb : b ≠ 0 := by
    intro hb
    apply ht 0 1 (by decide)
    refine ⟨a,fun l => ?_⟩
    fin_cases l <;> norm_num [pathFourth,hb,Fin.ext_iff]
  exact path_coefficient_cases a b
    (fun u v hu hv => path_ppm_facet_nonnegative a b u v h hu hv) hb

/-- Actual arbitrary-bias networks inherit the complete path orientation
and span necessity, with all input and first-row symmetries explicit. -/
theorem network_path_orientation_and_span (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (s₀ s₁ s₂ : Bool) (a b c : ℝ) (ht : Nonroot (pathFourth a b c))
    (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • (fun i => pathRows s₀ s₁ s₂ a b c (p j) (q i))) :
    (s₀ = true ∧ s₁ = true ∧ s₂ = false ∧ c = 0) ∨
    (s₀ = true ∧ s₁ = false ∧ s₂ = false ∧ a = 0) :=
  path_orientation_and_span s₀ s₁ s₂ a b c
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p s q hs hrows) ht

/-- Actual arbitrary-bias networks inherit the coefficient classification;
no restriction is imposed on their second-layer coefficients. -/
theorem network_canonical_path_coefficient_case (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (a b : ℝ) (ht : Nonroot (pathFourth a b 0))
    (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • (fun i => pathRows true true false a b 0 (p j) (q i))) :
    PathCoefficientCase a b :=
  canonical_path_coefficient_case a b
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p s q hs hrows) ht

/-- The normalized star's coordinate-zero condition is discharged using
the actual network before the orientation lemma is applied. -/
theorem network_star_orientation (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (b₁ b₂ b₃ : Bool) (t : Point 4) (hsum : ∑ i, t i = 0) (ht : Nonroot t)
    (p : Fin 6 → Fin 4) (s : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hs : ∀ j, (∑ i, net.W₁ j i) = 0 → 0 < s j)
    (hrows : ∀ j, (∑ i, net.W₁ j i) = 0 →
      net.W₁ j = s j • (fun i => starRows b₁ b₂ b₃ t (p j) (q i))) :
    b₁ = false ∧ b₂ = false ∧ b₃ = false :=
  star_orientation_forced b₁ b₂ b₃ t hsum ht
    (network_normalized_frame_cover net hnet _ p s q hs hrows)
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p s q hs hrows)

#print axioms network_normalized_frame_cover
#print axioms canonical_path_coefficient_case
#print axioms network_path_orientation_and_span
#print axioms network_canonical_path_coefficient_case
#print axioms network_star_orientation
end MaxCaterpillar.Fiber.Count65.ThreeRoots
