import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Paramid

/-! # Comparing paired outer maxima

Equal base values and equal analytic base germs imply equal outer germs.
This lets the block pairings compare the actual two-layer units without
assuming an outer apex/base tie.
-/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {m r s : ℕ}

theorem germ_max_eq_of_value_and_germ {f g : (Fin m → ℝ) → ℝ}
    {df dg : (Fin m → ℝ) → ℝ} (apex u : Fin m → ℝ)
    (hf : IsGerm f u df) (hg : IsGerm g u dg) (hv : f u = g u) (hd : df = dg) :
    germ (fun y => max (dot apex y) (f y)) u =
      germ (fun y => max (dot apex y) (g y)) u := by
  subst dg
  rcases lt_trichotomy (dot apex u) (f u) with hlt | heq | hgt
  · rw [germ_eq_of_isGerm (isGerm_max_of_lt (isGerm_dot apex u) hf hlt),
      germ_eq_of_isGerm (isGerm_max_of_lt (isGerm_dot apex u) hg (hv ▸ hlt))]
  · rw [germ_eq_of_isGerm (isGerm_max_of_eq (isGerm_dot apex u) hf heq),
      germ_eq_of_isGerm (isGerm_max_of_eq (isGerm_dot apex u) hg (heq.trans hv))]
  · have hleft : (fun y => max (dot apex y) (f y)) =
        fun y => max (f y) (dot apex y) := funext fun _ => max_comm _ _
    have hright : (fun y => max (dot apex y) (g y)) =
        fun y => max (g y) (dot apex y) := funext fun _ => max_comm _ _
    rw [hleft, hright,
      germ_eq_of_isGerm (isGerm_max_of_lt hf (isGerm_dot apex u) hgt),
      germ_eq_of_isGerm (isGerm_max_of_lt hg (isGerm_dot apex u) (hv ▸ hgt))]

theorem germ_caterpillarUnit_eq_of_base (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) (u : Fin m → ℝ)
    (hv : baseMax (values A u) S = baseMax (values B u) T)
    (hd : baseGerm A S u = baseGerm B T u) :
    germ (caterpillarUnit apex A S) u = germ (caterpillarUnit apex B T) u :=
  germ_max_eq_of_value_and_germ apex u (isGerm_baseMax A S u) (isGerm_baseMax B T u) hv hd

/-- Changing just one entering edge is invisible to the outer germ when
both versions of that edge expose the same strict endpoint. -/
theorem germ_caterpillarUnit_eq_of_pair_difference (apex : Fin m → ℝ)
    (A : Fin (r + 1) → Fin m → ℝ) (B : Fin (s + 1) → Fin m → ℝ)
    (S : Finset (Fin (r + 1))) (T : Finset (Fin (s + 1))) (u p q c : Fin m → ℝ)
    (hp : dot p u < dot c u) (hq : dot q u < dot c u)
    (he : ∀ y, baseMax (values B y) T - baseMax (values A y) S =
      max (dot p y) (dot c y) - max (dot q y) (dot c y)) :
    germ (caterpillarUnit apex A S) u = germ (caterpillarUnit apex B T) u := by
  have hpG := isGerm_max_of_lt (isGerm_dot p u) (isGerm_dot c u) hp
  have hqG := isGerm_max_of_lt (isGerm_dot q u) (isGerm_dot c u) hq
  have hfun : (fun y => baseMax (values B y) T) =
      (fun y => baseMax (values A y) S) +
        ((fun y => max (dot p y) (dot c y)) - (fun y => max (dot q y) (dot c y))) := by
    funext y
    have hy := he y
    change _ = _ + (_ - _)
    linarith only [hy]
  have hB : IsGerm (fun y => baseMax (values B y) T) u (baseGerm A S u) := by
    rw [hfun]
    simpa only [sub_self, add_zero] using (isGerm_baseMax A S u).add (hpG.sub hqG)
  have hv : baseMax (values A u) S = baseMax (values B u) T := by
    have h := he u
    rw [max_eq_right (le_of_lt hp), max_eq_right (le_of_lt hq), sub_self] at h
    exact (sub_eq_zero.mp h).symm
  exact germ_max_eq_of_value_and_germ apex u (isGerm_baseMax A S u) hB hv rfl

theorem germDiff_sub_mem_of_germ_eq {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} {k : ℕ}
    (hpos : germ f u = germ g u) (hf : germ f (-u) ∈ LSpan m k)
    (hg : germ g (-u) ∈ LSpan m k) : germDiff u f - germDiff u g ∈ LSpan m k := by
  have he : germDiff u f - germDiff u g = germ g (-u) - germ f (-u) := by
    rw [germDiff_eq_sub, germDiff_eq_sub, hpos]
    abel
  rw [he]
  exact Submodule.sub_mem _ hg hf

theorem germDiff_neg_direction (u : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) :
    germDiff (-u) f = -germDiff u f := by
  rw [germDiff_eq_sub, germDiff_eq_sub, neg_neg, neg_sub]

theorem germDiff_sub_mem_of_neg_direction {f g : (Fin m → ℝ) → ℝ}
    {u : Fin m → ℝ} {k : ℕ}
    (h : germDiff (-u) f - germDiff (-u) g ∈ LSpan m k) :
    germDiff u f - germDiff u g ∈ LSpan m k := by
  have hn := Submodule.neg_mem (LSpan m k) h
  simpa only [germDiff_neg_direction, neg_sub, neg_neg, neg_sub_neg] using hn

end MaxNN.Caterpillar
