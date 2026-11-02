import MaxCaterpillar.Fiber.Count65.TwoRoots.DirectedPath
import MaxCaterpillar.Fiber.Count65.TwoRoots.Outward
import MaxCaterpillar.Fiber.Count65.TwoRoots.Opposite
import MaxCaterpillar.Fiber.Count65.TwoRoots.Disjoint
import MaxCaterpillar.Fiber.Count65.TwoRoots.NetworkBridge
import MaxCaterpillar.Fiber.Count65.TripleLocality

/-! # The actual C3 omission condition supplies the two-root normalizations

The cover is a theorem of actual Max4 networks, not a classification premise.
Here it is used solely as the elementary coordinate omission property it states.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier BigOperators

lemma Represents.swap_last {r0 r1 s t : Point 4}
    (h : Represents ![r0,r1,s,t]) : Represents ![r0,r1,t,s] := by
  obtain ⟨ell,Phi,h⟩ := h
  refine ⟨ell,fun z => Phi ![z 0,z 1,z 3,z 2],fun x => ?_⟩
  have hstate :
      ![relu (lin (![r0,r1,t,s] 0) x),relu (lin (![r0,r1,t,s] 1) x),
        relu (lin (![r0,r1,t,s] 3) x),relu (lin (![r0,r1,t,s] 2) x)] =
      (fun j => relu (lin (![r0,r1,s,t] j) x)) := by
    funext j
    fin_cases j <;> rfl
  change Maximum 4 x = lin ell x + Phi _
  rw [hstate]
  exact h x

lemma cover_select_nonroot (r0 r1 s t : Point 4) (i : Fin 4)
    (h0 : r0 i ≠ 0) (h1 : r1 i ≠ 0)
    (hcover : ∀ k, ∃ j, (![r0,r1,s,t] : Fin 4 → Point 4) j k = 0) :
    s i = 0 ∨ t i = 0 := by
  obtain ⟨j,hj⟩ := hcover i
  fin_cases j
  · exact False.elim (h0 hj)
  · exact False.elim (h1 hj)
  · exact Or.inl hj
  · exact Or.inr hj

lemma omit1_nonzero (s : Point 4) (hsum : ∑ i, s i = 0)
    (hs : Nonroot s) (hs1 : s 1 = 0) : s 0 ≠ 0 ∧ s 2 ≠ 0 ∧ s 3 ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · intro hs0
    apply nonroot_not_supported_on_pair s hsum hs 2 3 (by decide)
    intro l hl2 hl3
    fin_cases l
    · exact hs0
    · exact hs1
    · exact False.elim (hl2 rfl)
    · exact False.elim (hl3 rfl)
  · intro hs2
    apply nonroot_not_supported_on_pair s hsum hs 0 3 (by decide)
    intro l hl0 hl3
    fin_cases l
    · exact False.elim (hl0 rfl)
    · exact hs1
    · exact hs2
    · exact False.elim (hl3 rfl)
  · intro hs3
    apply nonroot_not_supported_on_pair s hsum hs 0 2 (by decide)
    intro l hl0 hl2
    fin_cases l
    · exact False.elim (hl0 rfl)
    · exact hs1
    · exact False.elim (hl2 rfl)
    · exact hs3

lemma point_four_eq (s : Point 4) : ![s 0,s 1,s 2,s 3] = s := by
  funext i
  fin_cases i <;> rfl

lemma path_excluded_of_omit1 (s t : Point 4) (hsum : ∑ i,s i=0)
    (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t) (hs1 : s 1=0) :
    ¬ Represents ![![1,-1,0,0],![0,1,-1,0],s,t] := by
  have hsne := omit1_nonzero s hsum hs hs1
  have hsvec : s = ![s 0,0,s 2,s 3] := by
    rw [← hs1]; exact (point_four_eq s).symm
  have hrows : (![![1,-1,0,0],![0,1,-1,0],s,t] : Fin 4 → Point 4) =
      pathRows (s 0) (s 2) (s 3) (t 0) (t 1) (t 2) (t 3) := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact hsvec
    · exact (point_four_eq t).symm
  rw [hrows]
  exact directed_path_excluded _ _ _ _ _ _ _
    (by simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,hs1,add_assoc] using hsum)
    (by simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,add_assoc] using htsum)
    hsne.1 hsne.2.1 hsne.2.2 (by simpa only [point_four_eq] using ht)

/-- C3 excludes either assignment of the omitted-center nonroot to a path. -/
theorem covered_directed_path_excluded (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hcover : ∀ i, ∃ j,
      (![![1,-1,0,0],![0,1,-1,0],s,t] : Fin 4 → Point 4) j i=0) :
    ¬ Represents ![![1,-1,0,0],![0,1,-1,0],s,t] := by
  have ho := cover_select_nonroot ![1,-1,0,0] ![0,1,-1,0] s t 1
    (by norm_num) (by norm_num) hcover
  rcases ho with hs1 | ht1
  · exact path_excluded_of_omit1 s t hsum htsum hs ht hs1
  · intro h
    exact path_excluded_of_omit1 t s htsum hsum ht hs ht1 h.swap_last

lemma outward_excluded_of_omit1 (s t : Point 4) (hsum : ∑ i,s i=0)
    (hs : Nonroot s) (ht : Nonroot t) (hs1 : s 1=0) :
    ¬ Represents ![![-1,1,0,0],![0,1,-1,0],s,t] := by
  have hsne := omit1_nonzero s hsum hs hs1
  have hsvec : s = ![s 0,0,s 2,s 3] := by
    rw [← hs1]; exact (point_four_eq s).symm
  have hrows : (![![-1,1,0,0],![0,1,-1,0],s,t] : Fin 4 → Point 4) =
      outwardRows (s 0) (s 2) (s 3) t := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact hsvec
    · rfl
  rw [hrows]
  exact outward_fork_excluded _ _ _ t
    (by simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,hs1,add_assoc] using hsum) hsne.1 ht

/-- The C3 cover supplies the omitted-center row in the outward fork too. -/
theorem covered_outward_fork_excluded (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hcover : ∀ i, ∃ j,
      (![![-1,1,0,0],![0,1,-1,0],s,t] : Fin 4 → Point 4) j i=0) :
    ¬ Represents ![![-1,1,0,0],![0,1,-1,0],s,t] := by
  have ho := cover_select_nonroot ![-1,1,0,0] ![0,1,-1,0] s t 1
    (by norm_num) (by norm_num) hcover
  rcases ho with hs1 | ht1
  · exact outward_excluded_of_omit1 s t hsum hs ht hs1
  · intro h
    exact outward_excluded_of_omit1 t s htsum ht hs ht1 h.swap_last

lemma nonroot_omit01_false (s : Point 4) (hsum : ∑ i,s i=0)
    (hs : Nonroot s) (h0 : s 0=0) (h1 : s 1=0) : False := by
  apply nonroot_not_supported_on_pair s hsum hs 2 3 (by decide)
  intro l hl2 hl3
  fin_cases l
  · exact h0
  · exact h1
  · exact False.elim (hl2 rfl)
  · exact False.elim (hl3 rfl)

lemma opposite_excluded_of_omit1_omit0 (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hs1 : s 1=0) (ht0 : t 0=0) :
    ¬ Represents ![![1,-1,0,0],![-1,1,0,0],s,t] := by
  have hsne := omit1_nonzero s hsum hs hs1
  have hsvec : s = ![s 0,0,s 2,s 3] := by
    rw [← hs1]; exact (point_four_eq s).symm
  have htvec : t = ![0,t 1,t 2,t 3] := by
    rw [← ht0]; exact (point_four_eq t).symm
  have htne := triple_nonzero_of_nonroot (t 1) (t 2) (t 3)
    (by simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,ht0,add_assoc] using htsum)
    (by simpa only [← htvec] using ht)
  have hrows : (![![1,-1,0,0],![-1,1,0,0],s,t] : Fin 4 → Point 4) =
      oppositeRows (s 0) (s 2) (s 3) (t 1) (t 2) (t 3) := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact hsvec
    · exact htvec
  rw [hrows]
  exact opposite_roots_excluded _ _ _ _ _ _ hsne.2.1 hsne.2.2 htne.2.1
    (by simpa [Fin.sum_univ_succ,show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide,ht0,add_assoc] using htsum)

/-- C3 forces the two distinct omitted-coordinate assignments for opposite roots. -/
theorem covered_opposite_roots_excluded (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hcover : ∀ i, ∃ j,
      (![![1,-1,0,0],![-1,1,0,0],s,t] : Fin 4 → Point 4) j i=0) :
    ¬ Represents ![![1,-1,0,0],![-1,1,0,0],s,t] := by
  have ho0 := cover_select_nonroot ![1,-1,0,0] ![-1,1,0,0] s t 0
    (by norm_num) (by norm_num) hcover
  have ho1 := cover_select_nonroot ![1,-1,0,0] ![-1,1,0,0] s t 1
    (by norm_num) (by norm_num) hcover
  rcases ho0 with hs0 | ht0
  · rcases ho1 with hs1 | ht1
    · exact False.elim (nonroot_omit01_false s hsum hs hs0 hs1)
    · intro h
      exact opposite_excluded_of_omit1_omit0 t s htsum hsum ht hs ht1 hs0 h.swap_last
  · rcases ho1 with hs1 | ht1
    · exact opposite_excluded_of_omit1_omit0 s t hsum htsum hs ht hs1 ht0
    · exact False.elim (nonroot_omit01_false t htsum ht ht0 ht1)

/-- Coordinate omission is derived from the actual network, also after
positive first-row rescaling and arbitrary input permutation. -/
theorem network_coordinate_cover (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (A : Fin 4 → Point 4) (p : Fin 6 → Fin 4) (scale : Fin 6 → ℝ)
    (q : Equiv.Perm (Fin 4))
    (hscale : ∀ j, (∑ i,net.W₁ j i)=0 → 0<scale j)
    (hrows : ∀ j, (∑ i,net.W₁ j i)=0 →
      net.W₁ j=scale j • (fun i => A (p j) (q i))) :
    ∀ i, ∃ k, A k i=0 := by
  intro i
  obtain ⟨j,hj,hji,_⟩ := network_invariant_row_omits_coordinate net hnet (q.symm i)
  have hcoef := congrFun (hrows j hj) (q.symm i)
  simp only [Pi.smul_apply,smul_eq_mul,q.apply_symm_apply] at hcoef
  refine ⟨p j,?_⟩
  have hz : scale j * A (p j) i=0 := hcoef.symm.trans hji
  exact (mul_eq_zero.mp hz).resolve_left (hscale j hj).ne'

/-- Actual-network directed-path exclusion. The second-layer parameters and
all biases are unrestricted; C3 and factorization are proved consequences. -/
theorem network_directed_path_excluded (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i,net.W₁ j i)=0).card=4)
    (s t : Point 4) (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0)
    (hs : Nonroot s) (ht : Nonroot t)
    (p : Fin 6 → Fin 4) (scale : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hscale : ∀ j,(∑ i,net.W₁ j i)=0 → 0<scale j)
    (hrows : ∀ j,(∑ i,net.W₁ j i)=0 → net.W₁ j=scale j •
      (fun i => (![![1,-1,0,0],![0,1,-1,0],s,t] : Fin 4 → Point 4) (p j) (q i))) :
    False :=
  covered_directed_path_excluded s t hsum htsum hs ht
    (network_coordinate_cover net hnet _ p scale q hscale hrows)
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p scale q hscale hrows)

/-- Actual-network outward-fork exclusion, with both possible assignments
of the C3-forced nonroot included. -/
theorem network_outward_roots_excluded (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i,net.W₁ j i)=0).card=4)
    (s t : Point 4) (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0)
    (hs : Nonroot s) (ht : Nonroot t)
    (p : Fin 6 → Fin 4) (scale : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hscale : ∀ j,(∑ i,net.W₁ j i)=0 → 0<scale j)
    (hrows : ∀ j,(∑ i,net.W₁ j i)=0 → net.W₁ j=scale j •
      (fun i => (![![-1,1,0,0],![0,1,-1,0],s,t] : Fin 4 → Point 4) (p j) (q i))) :
    False :=
  covered_outward_fork_excluded s t hsum htsum hs ht
    (network_coordinate_cover net hnet _ p scale q hscale hrows)
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p scale q hscale hrows)

/-- Actual-network opposite-root exclusion with both C3 assignments derived. -/
theorem network_opposite_roots_excluded (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i,net.W₁ j i)=0).card=4)
    (s t : Point 4) (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0)
    (hs : Nonroot s) (ht : Nonroot t)
    (p : Fin 6 → Fin 4) (scale : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hscale : ∀ j,(∑ i,net.W₁ j i)=0 → 0<scale j)
    (hrows : ∀ j,(∑ i,net.W₁ j i)=0 → net.W₁ j=scale j •
      (fun i => (![![1,-1,0,0],![-1,1,0,0],s,t] : Fin 4 → Point 4) (p j) (q i))) :
    False :=
  covered_opposite_roots_excluded s t hsum htsum hs ht
    (network_coordinate_cover net hnet _ p scale q hscale hrows)
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p scale q hscale hrows)

/-- Actual-network complementary-root exclusion, with unrestricted suffix. -/
theorem network_disjoint_roots_excluded (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i,net.W₁ j i)=0).card=4)
    (s t : Point 4) (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0)
    (hs : Nonroot s) (ht : Nonroot t)
    (p : Fin 6 → Fin 4) (scale : Fin 6 → ℝ) (q : Equiv.Perm (Fin 4))
    (hscale : ∀ j,(∑ i,net.W₁ j i)=0 → 0<scale j)
    (hrows : ∀ j,(∑ i,net.W₁ j i)=0 → net.W₁ j=scale j •
      (fun i => disjointRows s t (p j) (q i))) : False :=
  disjoint_roots_excluded s t hsum htsum hs ht
    (network_represents_of_invariant_rows_permuted net hnet hcard _ p scale q hscale hrows)

#print axioms covered_opposite_roots_excluded
#print axioms network_opposite_roots_excluded
#print axioms network_disjoint_roots_excluded
#print axioms network_coordinate_cover
#print axioms network_directed_path_excluded
#print axioms network_outward_roots_excluded
#print axioms covered_directed_path_excluded
#print axioms covered_outward_fork_excluded
end MaxCaterpillar.Fiber.Count65.TwoRoots
