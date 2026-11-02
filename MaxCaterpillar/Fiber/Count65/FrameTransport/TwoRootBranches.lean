import MaxCaterpillar.Fiber.Count65.TwoRoots.InwardNormalization

/-! # Complete normalized two-root branch reduction

The rows following the two displayed roots are arbitrary real zero-sum
nonroots. C3 selects the omitted-center row in the inward fork; all
normalization coefficients are then obtained from the original factorization.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots

noncomputable def inwardPairRows (s t : Point 4) : Fin 4 → Point 4 :=
  ![![1,-1,0,0],![0,-1,1,0],s,t]

/-- The five canonical proper directed two-root graphs. Their numbering
agrees with `SmallRootFrames.twoCanonical`. -/
noncomputable def twoRootRows (k : Fin 5) (s t : Point 4) : Fin 4 → Point 4 :=
  if k.val = 0 then ![![1,-1,0,0],![0,0,1,-1],s,t]
  else if k.val = 1 then ![![1,-1,0,0],![-1,1,0,0],s,t]
  else if k.val = 2 then ![![1,-1,0,0],![0,1,-1,0],s,t]
  else if k.val = 3 then inwardPairRows s t
  else ![![-1,1,0,0],![0,1,-1,0],s,t]

/-- Information loss excludes four canonical root graphs. The inward
fork is the only remaining graph, before using the second-layer width. -/
theorem canonical_two_root_branch (k : Fin 5) (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hcover : ∀ i,∃ j,twoRootRows k s t j i=0)
    (h : Represents (twoRootRows k s t)) : k = 3 := by
  fin_cases k
  · apply False.elim
    exact disjoint_roots_excluded s t hsum htsum hs ht (by simpa [twoRootRows,disjointRows] using h)
  · apply False.elim
    exact covered_opposite_roots_excluded s t hsum htsum hs ht
      (by simpa [twoRootRows] using hcover) (by simpa [twoRootRows] using h)
  · apply False.elim
    exact covered_directed_path_excluded s t hsum htsum hs ht
      (by simpa [twoRootRows] using hcover) (by simpa [twoRootRows] using h)
  · rfl
  · apply False.elim
    exact covered_outward_fork_excluded s t hsum htsum hs ht
      (by simpa [twoRootRows] using hcover) (by simpa [twoRootRows] using h)

private theorem inward_of_omit1 (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0)
    (hs : Nonroot s) (ht : Nonroot t) (hs1 : s 1=0)
    (h : Represents (inwardPairRows s t)) :
    ∃ α β κ : ℝ,∃ scale : Fin 4→ℝ,
      0<α ∧ 0<β ∧ α+β=1 ∧ (∀ j,0<scale j) ∧
      (∀ j,inwardPairRows s t j=scale j • forkRows α β κ j) ∧
      max α β≤κ ∧ 0<κ ∧ κ≠1 ∧ Represents (forkRows α β κ) := by
  have hsne := omit1_nonzero s hsum hs hs1
  have hsvec : s = ![s 0,0,s 2,s 3] := by
    rw [←hs1]
    exact (point_four_eq s).symm
  have htvec : t = ![t 0,t 1,t 2,t 3] := (point_four_eq t).symm
  have hsraw : s 0+s 2+s 3=0 := by
    simpa [Fin.sum_univ_succ,hs1,add_assoc,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl] using hsum
  have htraw : t 0+t 1+t 2+t 3=0 := by
    simpa [Fin.sum_univ_succ,add_assoc,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl] using htsum
  have hA : inwardPairRows s t = inwardRows (s 0) (s 2) (s 3) (t 0) (t 1) (t 2) (t 3) := by
    funext j
    fin_cases j
    · rfl
    · rfl
    · exact hsvec
    · exact htvec
  have hcanon := inward_normalized_fork_constraints (s 0) (s 2) (s 3)
    (t 0) (t 1) (t 2) (t 3) hsraw htraw hsne.1 hsne.2.1
    (by rwa [←hsvec]) (by rwa [←htvec]) (by rwa [←hA])
  simpa only [←hA] using hcanon

/-- C3 selects one nonroot that omits the shared root coordinate. The
resulting row permutation is constructed, rather than assumed. Every scale
and every coefficient constraint comes from the original four observations. -/
theorem inward_pair_normalizes (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hcover : ∀ i,∃ j,inwardPairRows s t j i=0)
    (h : Represents (inwardPairRows s t)) :
    ∃ α β κ : ℝ,∃ p : Equiv.Perm (Fin 4),∃ scale : Fin 4→ℝ,
      0<α ∧ 0<β ∧ α+β=1 ∧ (∀ j,0<scale j) ∧
      (∀ j,inwardPairRows s t (p j)=scale j • forkRows α β κ j) ∧
      max α β≤κ ∧ 0<κ ∧ κ≠1 ∧ Represents (forkRows α β κ) := by
  have ho := cover_select_nonroot ![1,-1,0,0] ![0,-1,1,0] s t 1
    (by norm_num) (by norm_num) hcover
  rcases ho with hs1 | ht1
  · obtain ⟨α,β,κ,scale,hdata⟩ := inward_of_omit1 s t hsum htsum hs ht hs1 h
    exact ⟨α,β,κ,Equiv.refl _,scale,hdata⟩
  · have hswap : Represents (inwardPairRows t s) := h.swap_last
    obtain ⟨α,β,κ,scale,hα,hβ,hsum',hscale,hrows,hbound,hκ,hκne,hrep⟩ :=
      inward_of_omit1 t s htsum hsum ht hs ht1 hswap
    have hperm : ∀ j,inwardPairRows s t (Equiv.swap 2 3 j)=inwardPairRows t s j := by
      intro j
      fin_cases j <;>
        norm_num [inwardPairRows,Equiv.swap_apply_def,Fin.ext_iff,
          show (3 : Fin 4).val=3 from rfl]
    exact ⟨α,β,κ,Equiv.swap 2 3,scale,hα,hβ,hsum',hscale,
      fun j => (hperm j).trans (hrows j),hbound,hκ,hκne,hrep⟩

/-- The complete five-graph two-root reduction, with its normalization
constructed directly from the original arbitrary nonroot observations. -/
theorem canonical_two_root_normalizes (k : Fin 5) (s t : Point 4)
    (hsum : ∑ i,s i=0) (htsum : ∑ i,t i=0) (hs : Nonroot s) (ht : Nonroot t)
    (hcover : ∀ i,∃ j,twoRootRows k s t j i=0)
    (h : Represents (twoRootRows k s t)) :
    ∃ α β κ : ℝ,∃ p : Equiv.Perm (Fin 4),∃ scale : Fin 4→ℝ,
      0<α ∧ 0<β ∧ α+β=1 ∧ (∀ j,0<scale j) ∧
      (∀ j,twoRootRows k s t (p j)=scale j • forkRows α β κ j) ∧
      max α β≤κ ∧ 0<κ ∧ κ≠1 ∧ Represents (forkRows α β κ) := by
  have hk := canonical_two_root_branch k s t hsum htsum hs ht hcover h
  subst k
  simpa [twoRootRows] using inward_pair_normalizes s t hsum htsum hs ht
    (by simpa [twoRootRows] using hcover) (by simpa [twoRootRows] using h)

/-- One point makes all four normalized fork observations strictly negative.
Its unique target maximum is the root-center coordinate. -/
noncomputable def forkInactivePoint (κ : ℝ) : Point 4 := ![-1,0,-1,-(1+κ⁻¹)]

theorem fork_inactive_winner (κ : ℝ) (hκ : 0<κ) :
    forkInactivePoint κ 1 = Maximum 4 (forkInactivePoint κ) := by
  have hdiv : 0 < κ⁻¹ := inv_pos.mpr hκ
  rw [Maximum_four]
  change 0 = max (max (-1 : ℝ) 0) (max (-1) (-(1+κ⁻¹)))
  rw [show max (-1 : ℝ) 0 = 0 from max_eq_right (by norm_num),
    show max (-1 : ℝ) (-(1+κ⁻¹)) = -1 from max_eq_left (by linarith only [hdiv]),
    show max (0 : ℝ) (-1) = 0 from max_eq_left (by norm_num)]

theorem fork_all_strictly_inactive (α β κ : ℝ) (hsum : α+β=1) (hκ : 0<κ) :
    ∀ j,lin (forkRows α β κ j) (forkInactivePoint κ)<0 := by
  have hdiv : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hprod : κ*κ⁻¹=1 := mul_inv_cancel (ne_of_gt hκ)
  intro j
  fin_cases j
  · norm_num [lin_four,forkRows,forkInactivePoint]
  · norm_num [lin_four,forkRows,forkInactivePoint]
  · simp [lin_four,forkRows,forkInactivePoint]
    linarith only [hsum,hdiv]
  · simp [lin_four,forkRows,forkInactivePoint]
    nlinarith only [hsum,hprod,hκ]

#check @canonical_two_root_branch
#check @inward_pair_normalizes
#check @canonical_two_root_normalizes
#check @fork_inactive_winner
#check @fork_all_strictly_inactive
#print axioms canonical_two_root_branch
#print axioms inward_pair_normalizes
#print axioms canonical_two_root_normalizes
#print axioms fork_inactive_winner
#print axioms fork_all_strictly_inactive
end MaxCaterpillar.Fiber.Count65.FrameTransport
