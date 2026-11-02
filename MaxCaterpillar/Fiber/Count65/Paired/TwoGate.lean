import MaxCaterpillar.Frontier.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Two affine ReLU gates on a convex domain

A sign-changing affine target represented by one positive and one negative
ReLU is either an opposite signed pair or a pair nonnegative throughout the
domain. The proof extends affine equalities along short segments; it needs
neither full dimensionality nor a recession case split.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired
open Filter Topology Frontier
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private lemma affine_combo (f : V →ᵃ[ℝ] ℝ) (x y : V) (t : ℝ) :
    f ((1-t) • x + t • y) = (1-t)*f x+t*f y := by
  rw [← AffineMap.lineMap_apply_module, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring]

/-- A nonempty strict affine patch determines any other affine function on
an arbitrary convex domain, including a domain with empty ambient interior. -/
theorem affine_zero_of_positive_patch (C : Set V) (hC : Convex ℝ C)
    (F u v : V →ᵃ[ℝ] ℝ) (x : V) (hx : x∈C) (hu : 0<u x) (hv : 0<v x)
    (hzero : ∀ z∈C, 0<u z → 0<v z → F z=0) : ∀ y∈C, F y=0 := by
  intro y hy
  have hFx := hzero x hx hu hv
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |t*(u y-u x)| < u x ∧ |t*(v y-v x)| < v x ∧ t∈Set.Ioo (0:ℝ) 1 :=
    (eventually_small (u y-u x) hu).and
      ((eventually_small (v y-v x) hv).and
        (Ioo_mem_nhdsWithin_Ioi (by norm_num)))
  obtain ⟨t,htu,htv,ht0,ht1⟩ := hall.exists
  let z := (1-t) • x+t • y
  have hz : z∈C := hC hx hy (by linarith only [ht1]) ht0.le (by ring)
  have huz : 0<u z := by
    dsimp only [z]
    rw [affine_combo]
    have hh := (abs_lt.mp htu).1
    nlinarith only [hh]
  have hvz : 0<v z := by
    dsimp only [z]
    rw [affine_combo]
    have hh := (abs_lt.mp htv).1
    nlinarith only [hh]
  have hfz := hzero z hz huz hvz
  dsimp only [z] at hfz
  rw [affine_combo, hFx] at hfz
  have : t*F y=0 := by simpa using hfz
  exact (mul_eq_zero.mp this).resolve_left (ne_of_gt ht0)

/-- Complete two-gate classification for any sign-changing affine target on
a convex domain. There is no assumption on the two gate activation regions. -/
theorem two_gate_affine_classification (C : Set V) (hC : Convex ℝ C)
    (g h L : V →ᵃ[ℝ] ℝ)
    (hpos : ∃ x∈C, 0<L x) (hneg : ∃ x∈C, L x<0)
    (heq : ∀ x∈C, relu (g x)-relu (h x)=L x) :
    (∀ x∈C, g x=L x ∧ h x= -L x) ∨
      (∀ x∈C, 0≤g x ∧ 0≤h x ∧ g x-h x=L x) := by
  classical
  by_cases hpatch : ∃ x∈C, 0<L x ∧ 0<h x
  · obtain ⟨x,hx,hLx,hhx⟩ := hpatch
    have hdiff : ∀ y∈C, g y-h y=L y := by
      have hz := affine_zero_of_positive_patch C hC (g-h-L) L h x hx hLx hhx
        (by
          intro z hz hLz hhz
          have hh := heq z hz
          have hgz : 0<g z := by
            by_contra hn
            rw [relu_of_nonpos (le_of_not_gt hn), relu_of_nonneg hhz.le] at hh
            linarith only [hh,hLz,hhz]
          rw [relu_of_nonneg hgz.le, relu_of_nonneg hhz.le] at hh
          change g z-h z-L z=0
          linarith only [hh])
      intro y hy
      have hh := hz y hy
      change g y-h y-L y=0 at hh
      linarith only [hh]
    have hnonneg : ∀ y∈C, 0≤g y ∧ 0≤h y := by
      intro y hy
      by_contra hn
      have hboth : g y<0 ∧ h y<0 := by
        have hh := heq y hy
        have hd := hdiff y hy
        by_cases hg : 0≤g y
        · have hhneg : h y<0 := lt_of_not_ge (fun hh => hn ⟨hg,hh⟩)
          rw [relu_of_nonneg hg, relu_of_nonpos hhneg.le] at hh
          linarith only [hh,hd,hhneg]
        · have hgneg := lt_of_not_ge hg
          by_cases hh0 : 0≤h y
          · rw [relu_of_nonpos hgneg.le, relu_of_nonneg hh0] at hh
            linarith only [hh,hd,hgneg]
          · exact ⟨hgneg,lt_of_not_ge hh0⟩
      have hz := affine_zero_of_positive_patch C hC L (-g) (-h) y hy
        (by simpa using neg_pos.mpr hboth.1)
        (by simpa using neg_pos.mpr hboth.2)
        (by
          intro z hz hgz hhz
          change 0< -g z at hgz
          change 0< -h z at hhz
          have hh := heq z hz
          rw [relu_of_nonpos (by linarith only [hgz]),
            relu_of_nonpos (by linarith only [hhz])] at hh
          linarith only [hh])
      obtain ⟨z,hzmem,hzpos⟩ := hpos
      have hh := hz z hzmem
      linarith only [hh,hzpos]
    exact Or.inr (fun y hy => ⟨(hnonneg y hy).1,(hnonneg y hy).2,hdiff y hy⟩)
  · have hg : ∀ y∈C, g y=L y := by
      obtain ⟨x,hx,hLx⟩ := hpos
      have hz := affine_zero_of_positive_patch C hC (g-L) L L x hx hLx hLx
        (by
          intro z hz hLz _
          have hhz : h z≤0 := le_of_not_gt (fun hh => hpatch ⟨z,hz,hLz,hh⟩)
          have hh := heq z hz
          rw [relu_of_nonpos hhz, sub_zero] at hh
          have hgz : 0≤g z := by
            by_contra hn
            rw [relu_of_nonpos (le_of_not_ge hn)] at hh
            linarith only [hh,hLz]
          rw [relu_of_nonneg hgz] at hh
          change g z-L z=0
          linarith only [hh])
      intro y hy
      have hh := hz y hy
      change g y-L y=0 at hh
      linarith only [hh]
    have hh : ∀ y∈C, h y= -L y := by
      obtain ⟨x,hx,hLx⟩ := hneg
      have hz := affine_zero_of_positive_patch C hC (h+L) (-L) (-L) x hx
        (by simpa using neg_pos.mpr hLx) (by simpa using neg_pos.mpr hLx)
        (by
          intro z hz hLz _
          change 0< -L z at hLz
          have he := heq z hz
          rw [hg z hz, relu_of_nonpos (by linarith only [hLz])] at he
          have hhz : 0≤h z := by
            by_contra hn
            rw [relu_of_nonpos (le_of_not_ge hn)] at he
            linarith only [he,hLz]
          rw [relu_of_nonneg hhz] at he
          change h z+L z=0
          linarith only [he])
      intro y hy
      have he := hz y hy
      change h y+L y=0 at he
      linarith only [he]
    exact Or.inl (fun y hy => ⟨hg y hy,hh y hy⟩)

end MaxCaterpillar.Fiber.Count65.Paired
