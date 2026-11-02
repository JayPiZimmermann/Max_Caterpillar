import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.GapPolynomial

/-! # Adjacent actual tail swaps and source prefix coefficients

Only the prefix separating the two adjacent positions changes. Its change is
an exact real identity. Negation requires the two neighboring source prefixes
to vanish; no unconditional absolute-value invariance is asserted.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

/-- Extended source prefix, including threshold zero and the full-tail boundary. -/
noncomputable def prefixCoeff {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (n : ℕ) : ℝ :=
  w none+∑ k in Finset.univ.filter (fun k : Fin m => k.val<n),w (some (p.1 k))

/-- Swap the two actual positions in tau and keep the original rho unchanged. -/
noncomputable def swapAdjacentConfig {m : ℕ} (p : RawConfig m) (a b : Fin m) : RawConfig m :=
  ((Equiv.swap a b).trans p.1,p.2)

lemma swapAdjacentConfig_tau {m : ℕ} (p : RawConfig m) (a b k : Fin m) :
    (swapAdjacentConfig p a b).1 k=p.1 (Equiv.swap a b k) := rfl

lemma swapAdjacentConfig_rho {m : ℕ} (p : RawConfig m) (a b : Fin m) :
    (swapAdjacentConfig p a b).2=p.2 := rfl

private lemma prefix_sum_swap {m : ℕ} (f : Fin m→ℝ) (a b : Fin m) (hab : a≠b) (n : ℕ) :
    (∑ k : Fin m,if k.val<n then f (Equiv.swap a b k) else 0)=
      (∑ k : Fin m,if k.val<n then f k else 0)+
      (if a.val<n then f b-f a else 0)+(if b.val<n then f a-f b else 0) := by
  classical
  have hpoint (k : Fin m) :
      (if k.val<n then f (Equiv.swap a b k) else 0)=
        (if k.val<n then f k else 0)+
        (if k=a then (if a.val<n then f b-f a else 0) else 0)+
        (if k=b then (if b.val<n then f a-f b else 0) else 0) := by
    by_cases hka : k=a
    · subst k
      by_cases ha : a.val<n <;>
        simp only [Equiv.swap_apply_left,if_pos rfl,if_neg hab,ha,if_true,if_false] <;> ring
    · by_cases hkb : k=b
      · subst k
        by_cases hb : b.val<n <;>
          simp only [Equiv.swap_apply_right,if_neg (Ne.symm hab),if_pos rfl,hb,if_true,if_false] <;> ring
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
        simp only [if_neg hka,if_neg hkb,add_zero]
  have hs : (∑ k : Fin m,if k.val<n then f (Equiv.swap a b k) else 0)=
      ∑ k : Fin m,((if k.val<n then f k else 0)+
        (if k=a then (if a.val<n then f b-f a else 0) else 0)+
        (if k=b then (if b.val<n then f a-f b else 0) else 0)) :=
    Finset.sum_congr rfl (fun k _ => hpoint k)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hs

/-- The general exact swap difference, before using adjacency. -/
theorem prefixCoeff_swap_difference {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (a b : Fin m) (hab : a≠b) (n : ℕ) :
    prefixCoeff (swapAdjacentConfig p a b) w n=prefixCoeff p w n+
      (if a.val<n then w (some (p.1 b))-w (some (p.1 a)) else 0)+
      (if b.val<n then w (some (p.1 a))-w (some (p.1 b)) else 0) := by
  have hs := prefix_sum_swap (fun k => w (some (p.1 k))) a b hab n
  unfold prefixCoeff
  simp only [swapAdjacentConfig,Equiv.trans_apply,Finset.sum_filter]
  rw [hs]
  ring

private lemma adjacent_ne {m : ℕ} (a b : Fin m) (hab : a.val+1=b.val) : a≠b := by
  intro he
  have hv := congrArg Fin.val he
  have hh : a.val+1=a.val := hab.trans hv.symm
  exact Nat.succ_ne_self _ hh

/-- Away from the separating threshold, adjacent tail swaps preserve the prefix. -/
theorem prefixCoeff_swap_of_ne {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (a b : Fin m) (hab : a.val+1=b.val) (n : ℕ) (hn : n≠b.val) :
    prefixCoeff (swapAdjacentConfig p a b) w n=prefixCoeff p w n := by
  rw [prefixCoeff_swap_difference p w a b (adjacent_ne a b hab) n]
  have hlt : a.val<b.val := by rw [← hab]; exact Nat.lt_succ_self _
  by_cases ha : a.val<n
  · by_cases hb : b.val<n
    · simp only [if_pos ha,if_pos hb]
      ring
    · have hbn : b.val≤n := by rw [← hab]; exact Nat.succ_le_iff.mpr ha
      have hnb : n≤b.val := not_lt.mp hb
      exact False.elim (hn (Nat.le_antisymm hnb hbn))
  · have hb : ¬b.val<n := fun h => ha (lt_trans hlt h)
    simp only [if_neg ha,if_neg hb,add_zero]

/-- Every other actual gap prefix is unchanged by this adjacent swap. -/
theorem prefixCoeff_swap_other_gap {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (a b : Fin m) (hab : a.val+1=b.val) (g : Fin m) (hg : g≠b) :
    prefixCoeff (swapAdjacentConfig p a b) w g.val=prefixCoeff p w g.val :=
  prefixCoeff_swap_of_ne p w a b hab g.val (fun he => hg (Fin.ext he))

/-- At the separating gap, the first tail weight is replaced by the second. -/
theorem prefixCoeff_swap_at_cut {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (a b : Fin m) (hab : a.val+1=b.val) :
    prefixCoeff (swapAdjacentConfig p a b) w b.val=
      prefixCoeff p w b.val+w (some (p.1 b))-w (some (p.1 a)) := by
  rw [prefixCoeff_swap_difference p w a b (adjacent_ne a b hab) b.val]
  have hlt : a.val<b.val := by rw [← hab]; exact Nat.lt_succ_self _
  simp only [if_pos hlt,lt_self_iff_false,if_false,add_zero]
  ring

/-- One source-prefix step, including the final step to threshold m. -/
theorem prefixCoeff_succ {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ) (a : Fin m) :
    prefixCoeff p w (a.val+1)=prefixCoeff p w a.val+w (some (p.1 a)) := by
  classical
  have hf : Finset.univ.filter (fun k : Fin m => k.val<a.val+1)=
      insert a (Finset.univ.filter (fun k : Fin m => k.val<a.val)) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Nat.lt_succ_iff]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | he
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext he)
    · rintro (rfl | hlt)
      · exact le_rfl
      · exact hlt.le
  have hn : a∉Finset.univ.filter (fun k : Fin m => k.val<a.val) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,lt_self_iff_false,not_false_eq_true]
  unfold prefixCoeff
  rw [hf,Finset.sum_insert hn]
  ring

/-- At the full-tail boundary, the source prefix is the complete original row sum. -/
theorem prefixCoeff_at_card {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ) :
    prefixCoeff p w m=∑ x : Option (Fin m),w x := by
  classical
  have hf : Finset.univ.filter (fun k : Fin m => k.val<m)=Finset.univ := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact k.isLt
  unfold prefixCoeff
  rw [hf,Equiv.sum_comp p.1 (fun a => w (some a)),Fintype.sum_option]

/-- Negation follows from the supplied two neighboring-zero conditions;
the right condition is a natural threshold even at the full-tail boundary. -/
theorem prefixCoeff_swap_neg_of_neighbors {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (a b : Fin m) (hab : a.val+1=b.val)
    (hleft : prefixCoeff p w a.val=0) (hright : prefixCoeff p w (b.val+1)=0) :
    prefixCoeff (swapAdjacentConfig p a b) w b.val= -prefixCoeff p w b.val := by
  have ha := prefixCoeff_succ p w a
  rw [hab,hleft,zero_add] at ha
  have hb := prefixCoeff_succ p w b
  rw [hright] at hb
  have hc := prefixCoeff_swap_at_cut p w a b hab
  linarith only [ha,hb,hc]

/-- Source gap coefficients agree with extended prefixes under the full zero sum. -/
theorem tailCoefficient_eq_prefixCoeff {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (hzero : (∑ x : Option (Fin m),w x)=0) (g : Fin m) :
    tailCoefficient p w g=prefixCoeff p w g.val :=
  tailCoefficient_eq_prefix p w hzero g

theorem tailCoefficient_swap_other_gap {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (hzero : (∑ x : Option (Fin m),w x)=0)
    (a b : Fin m) (hab : a.val+1=b.val) (g : Fin m) (hg : g≠b) :
    tailCoefficient (swapAdjacentConfig p a b) w g=tailCoefficient p w g := by
  rw [tailCoefficient_eq_prefixCoeff _ _ hzero,tailCoefficient_eq_prefixCoeff _ _ hzero]
  exact prefixCoeff_swap_other_gap p w a b hab g hg

theorem tailCoefficient_swap_at_cut {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (hzero : (∑ x : Option (Fin m),w x)=0)
    (a b : Fin m) (hab : a.val+1=b.val) :
    tailCoefficient (swapAdjacentConfig p a b) w b=
      tailCoefficient p w b+w (some (p.1 b))-w (some (p.1 a)) := by
  rw [tailCoefficient_eq_prefixCoeff _ _ hzero,tailCoefficient_eq_prefixCoeff _ _ hzero]
  exact prefixCoeff_swap_at_cut p w a b hab

theorem tailCoefficient_swap_neg_of_neighbors {m : ℕ} (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (hzero : (∑ x : Option (Fin m),w x)=0)
    (a b : Fin m) (hab : a.val+1=b.val)
    (hleft : prefixCoeff p w a.val=0) (hright : prefixCoeff p w (b.val+1)=0) :
    tailCoefficient (swapAdjacentConfig p a b) w b= -tailCoefficient p w b := by
  rw [tailCoefficient_eq_prefixCoeff _ _ hzero,tailCoefficient_eq_prefixCoeff _ _ hzero]
  exact prefixCoeff_swap_neg_of_neighbors p w a b hab hleft hright

/-- The right boundary condition follows from the original total zero sum when
b is the final position; no fictitious gap index m is introduced. -/
theorem tailCoefficient_swap_neg_at_right_boundary {m : ℕ} (p : RawConfig m)
    (w : Option (Fin m)→ℝ) (hzero : (∑ x : Option (Fin m),w x)=0)
    (a b : Fin m) (hab : a.val+1=b.val) (hboundary : b.val+1=m)
    (hleft : prefixCoeff p w a.val=0) :
    tailCoefficient (swapAdjacentConfig p a b) w b= -tailCoefficient p w b := by
  apply tailCoefficient_swap_neg_of_neighbors p w hzero a b hab hleft
  rw [hboundary,prefixCoeff_at_card,hzero]
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
