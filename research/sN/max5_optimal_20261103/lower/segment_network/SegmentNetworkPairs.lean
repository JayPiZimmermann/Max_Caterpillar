import research.sN.max5_optimal_20261103.lower.segment_network.SegmentNetworkGeneral

/-! Coordinate-permutation bridge: the guarded segment condition applies
to every distinct pair of Max5 contact labels, not only labels3,4. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact

lemma exists_pair_reindex (i j : Fin 5) (hij : i≠j) :
    ∃ e : Equiv.Perm (Fin 5), e 3=i ∧ e 4=j := by
  let e : Equiv.Perm (Fin 5) := Equiv.swap 3 i
  have hb : (3 : Fin 5)≠e.symm j := by
    intro h
    have hh := congrArg e h
    rw [Equiv.apply_symm_apply] at hh
    exact hij (by simpa only [e,Equiv.swap_apply_left] using hh)
  let f : Equiv.Perm (Fin 5) := Equiv.swap 4 (e.symm j)
  refine ⟨f.trans e,?_,?_⟩
  · change e (f 3)=i
    rw [show f 3=3 from Equiv.swap_apply_of_ne_of_ne (by decide) hb]
    exact Equiv.swap_apply_left _ _
  · change e (f 4)=j
    rw [show f 4=e.symm j from Equiv.swap_apply_left _ _]
    exact e.apply_symm_apply j

lemma lin_relabel (a : Point 5) (e : Equiv.Perm (Fin 5)) (x : Point 5) :
    lin (fun i => a (e i)) x=lin a (fun i => x (e.symm i)) := by
  unfold lin
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

lemma core_relabel {m : ℕ} (A : Fin m → Point 5) (c : Fin m → ℝ)
    (e : Equiv.Perm (Fin 5)) (x : Point 5) :
    core (fun j i => A j (e i)) c x=core A c (fun i => x (e.symm i)) := by
  simp only [core,lin_relabel]

lemma shallow_relabel {m : ℕ} (a : Point 5) (b : ℝ)
    (A : Fin m → Point 5) (β c : Fin m → ℝ)
    (e : Equiv.Perm (Fin 5)) (x : Point 5) :
    shallow (fun i => a (e i)) b (fun j i => A j (e i)) β c x=
      shallow a b A β c (fun i => x (e.symm i)) := by
  simp only [shallow,lin_relabel]

lemma maximum_relabel (e : Equiv.Perm (Fin 5)) (x : Point 5) :
    Maximum 5 (fun i => x (e.symm i))=Maximum 5 x := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    exact le_Maximum x (e.symm i)
  · apply (Maximum_le_iff _ _).mpr
    intro i
    simpa only [e.symm_apply_apply] using
      le_Maximum (fun j => x (e.symm j)) (e i)

noncomputable def pairMidpointMass {m : ℕ} (A : Fin m → Point 5)
    (c : Fin m → ℝ) (k : Fin m) (i j : Fin 5) : ℝ :=
  ∑ l in Finset.univ.erase k, c l*midpointWeight (A l i) (A l j)

/-- The exact guarded clause for any distinct pair of shared contacts.
Every permutation is performed on the actual row arrays and target. -/
theorem balance_or_zero_pair_mass {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (i j : Fin 5) (hij : i≠j)
    (hrows : ∀ l, l≠k → A l i=0 ∨ A l j=0 ∨ A l i+A l j=0)
    (hci : core A c (-unitVec i)=0) (hcj : core A c (-unitVec j)=0)
    (hdi : core A d (-unitVec i)=0) (hdj : core A d (-unitVec j)=0)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) :
    pairMidpointMass A c k i j=0 ∨ pairMidpointMass A d k i j=0 ∨ A k i+A k j=0 := by
  obtain ⟨e,he3,he4⟩ := exists_pair_reindex i j hij
  let A' := fun l t => A l (e t)
  have hrows' : ∀ l, l≠k → A' l 3=0 ∨ A' l 4=0 ∨ A' l 3+A' l 4=0 := by
    intro l hl
    simpa only [A',he3,he4] using hrows l hl
  have hc3 : core A' c (-unitVec (3 : Fin 5))=0 := by
    simpa only [core,lin_neg_right,lin_unitVec,A',he3] using hci
  have hc4 : core A' c (-unitVec (4 : Fin 5))=0 := by
    simpa only [core,lin_neg_right,lin_unitVec,A',he4] using hcj
  have hd3 : core A' d (-unitVec (3 : Fin 5))=0 := by
    simpa only [core,lin_neg_right,lin_unitVec,A',he3] using hdi
  have hd4 : core A' d (-unitVec (4 : Fin 5))=0 := by
    simpa only [core,lin_neg_right,lin_unitVec,A',he4] using hdj
  have heq' : ∀ x, shallow (fun t => aR (e t)) bR (fun l t => AR l (e t)) βR cR x+
      relu (core A' c x)+relu (core A' d x)=Maximum 5 x := by
    intro x
    rw [shallow_relabel,core_relabel,core_relabel,heq,maximum_relabel]
  have h := balance_or_zero_midpoint_mass A' c d k (fun t => aR (e t)) bR
    (fun l t => AR l (e t)) βR cR hrows' hc3 hc4 hd3 hd4 heq'
  simpa only [midpointMass,pairMidpointMass,A',he3,he4] using h

#check @balance_or_zero_pair_mass
#print axioms balance_or_zero_pair_mass
end MaxCaterpillar.Max5Optimal.SegmentNetwork
