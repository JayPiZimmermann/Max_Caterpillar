import MaxNN.Constructions.Paramid.Geom.Flag
import MaxNN.Constructions.Paramid.Geom.Reconstruct
import MaxNN.Constructions.Paramid.Geom.Sweep
import MaxNN.Constructions.Paramid.Geom.Complete.Chart

/-!
# Completeness of the flag functionals (module M-Complete)

Module `M-Complete` of the geometric core (`work/depth2_simplex/lean_core/BLUEPRINT.md`; paper
level: `work/depth2_simplex/CONSTRUCTIVE_SWEEP_RECONSTRUCTION_2026-10-13.md`, Theorem 4.1
(DECOMPOSE), with the vertical-cut reconstruction replaced by `simplex_reconstruct_any_height`).

**Theorem** (`mem_LSpan_of_flagFun_eq_zero`, exactly the blueprint statement).  Let `m ≥ 1` and
let `f = ∑ᵢ aᵢ h_{Pᵢ}` be a finite real combination of support functions of `m`-simplices
`Pᵢ = conv (Pᵢ 0, …, Pᵢ m) ⊂ ℝ^m`.  If every flag functional of `ℝ^m` vanishes on `f`
(`flagFun us f = 0` for every `IsFlag us`), then `f` is a combination of support functions of
point sets of affine dimension `≤ m − 1` (`f ∈ LSpan m (m − 1)`).

Added for the downstream modules: `mem_LSpan_of_flagFun_eq_zero_of_sub_mem`, the same conclusion
for any `f ∈ SSpan m` that agrees with such a simplex combination modulo `LSpan m (m − 1)` (the
form needed after the Kuhn decomposition of the paramid cones).

## Proof (induction on `m`, `CompleteIn m`)

* `m = 1` (`completeIn_one`): the flag `[1]` gives `f(1) + f(−1) = 0`; by positive homogeneity
  `f(y) = y₀ f(1)` for `y₀ ≥ 0` and `f(y) = −y₀ f(−1)` for `y₀ < 0`, so `f` is linear.
* `m = n + 1`, `n ≥ 1` (`completeIn_succ`): sweep along `v = w = e₀`.
  1. The reconstruction `simplex_reconstruct_any_height` writes each `h_{Pᵢ}` as
     `∑_j ε_{ij} 𝒯 h_{F_{ij}}` modulo `LSpan (n + 1) n` (`F_{ij}` the facets, `ε_{ij}` their
     signs along `e₀`).  So `f − 𝒯 g ∈ LSpan (n + 1) n` with `g = ∑ᵢ aᵢ ∑_j ε_{ij} h_{F_{ij}}`, and
     since `𝒯` raises the dimension by at most one (`sweep_mem_LSpan`), it suffices to show
     `g ∈ LSpan (n + 1) (n − 1)`.
  2. Group the facets by their direction `ν = facetDir` (the facet normal normalized against
     `e₀`).  The vertical facets (`⟨ν, e₀⟩ ≠ 1`) carry the sign `0`.
  3. For a transverse direction `ν` (`ν 0 = 1`), the group `g_ν` lives in the hyperplanes
     `{⟨ν, ·⟩ = c}` and reads, in the chart `chartT ν` (delete the coordinate `0`), as
     `g_ν = G ∘ chartT ν + (linear)`, `G` a combination of `n`-simplices of `ℝ^n`
     (`CompleteAux.group_mem_LSpan`).  Every flag `us` of `ℝ^n` lifts to the flag `ν :: (0, us)`
     of `ℝ^{n+1}`,
     and `Λ_{ν :: (0, us)} f = Λ_{(0, us)} (germDiff ν f) = Λ_{(0, us)} g_ν = Λ_{us} G` by the
     grouping lemma `germDiff_hS_simplex_sub_mem_LSpan` (the facet datum of a simplex in direction
     `ν` is its facet of direction `ν`, modulo `LSpan (n + 1) (n − 1)`, which flag functionals of
     length `n` do not see).  So all flag functionals of `G` vanish, the induction hypothesis
     gives `G ∈ LSpan n (n − 1)`, and `g_ν ∈ LSpan (n + 1) (n − 1)`.

The chart, the flag lifting and the bookkeeping are in `Geom/Complete/Chart.lean`.
-/

namespace MaxNN.ParamidGeom

open BigOperators
open scoped Matrix

noncomputable section

open CompleteAux

/-- **The completeness statement in dimension `m`:** a finite combination of support functions
of `m`-simplices of `ℝ^m` on which every flag functional vanishes lies in `LSpan m (m − 1)`. -/
def CompleteIn (m : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ) (P : ι → Fin (m + 1) → Fin m → ℝ),
    (∀ i, AffineIndependent ℝ (P i)) →
    (∀ us, IsFlag us → flagFun us (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) = 0) →
    (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) ∈ LSpan m (m - 1)

/-! ## Dimension one -/

/-- **Completeness in dimension one:** a combination of support functions of segments of `ℝ`
whose total signed length vanishes is linear. -/
theorem completeIn_one : CompleteIn 1 := by
  intro ι _ a P _ hflag
  have hne : ∀ i, (Finset.univ.image (P i)).Nonempty := fun i => Finset.univ_nonempty.image _
  have hu0 : (fun _ => (1 : ℝ) : Fin 1 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    exact one_ne_zero h0
  have h1 := hflag [fun _ => 1] ((isFlag_singleton_iff _).mpr hu0)
  have h2 : ∀ i, flagFun [(fun _ => (1 : ℝ) : Fin 1 → ℝ)]
      (fun y => a i * hS (Finset.univ.image (P i)) y) =
      a i * hS (Finset.univ.image (P i)) (fun _ => 1) +
        a i * hS (Finset.univ.image (P i)) (-fun _ => 1) := by
    intro i
    rw [flagFun_const_mul (a i) (GermAux.hS_mem_SSpan (hne i)), flagFun_singleton_hS (hne i),
      mul_add]
  have hval : flagFun [(fun _ => (1 : ℝ) : Fin 1 → ℝ)]
      (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) =
      ∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1) +
        ∑ i, a i * hS (Finset.univ.image (P i)) (-fun _ => 1) := by
    rw [flagFun_sum Finset.univ (f := fun i y => a i * hS (Finset.univ.image (P i)) y)
      (fun i _ => Submodule.smul_mem _ (a i) (GermAux.hS_mem_SSpan (hne i))),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => h2 i
  rw [hval] at h1
  -- `f` is linear: `f y = f(1) y₀`
  have hlin : (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) =
      dot (fun _ => ∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1)) := by
    funext y
    have hdot : dot (fun _ => ∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1)) y =
        (∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1)) * y 0 := by
      show ∑ k : Fin 1, (∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1)) * y k = _
      rw [Fin.sum_univ_one]
    rw [hdot]
    rcases le_or_lt 0 (y 0) with hy | hy
    · have e : y = y 0 • (fun _ => (1 : ℝ) : Fin 1 → ℝ) := by
        funext k
        rw [Fin.eq_zero k]
        simp
      calc ∑ i, a i * hS (Finset.univ.image (P i)) y
          = ∑ i, a i * hS (Finset.univ.image (P i)) (y 0 • (fun _ => (1 : ℝ) : Fin 1 → ℝ)) := by
            rw [← e]
        _ = (∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1)) * y 0 := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hS_smul_of_nonneg _ hy]
            ring
    · have e : y = (-y 0) • (-fun _ => (1 : ℝ) : Fin 1 → ℝ) := by
        funext k
        rw [Fin.eq_zero k]
        simp
      have hneg : ∑ i, a i * hS (Finset.univ.image (P i)) (-fun _ => 1) =
          -∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1) := by
        linarith
      calc ∑ i, a i * hS (Finset.univ.image (P i)) y
          = ∑ i, a i * hS (Finset.univ.image (P i))
              ((-y 0) • (-fun _ => (1 : ℝ) : Fin 1 → ℝ)) := by
            rw [← e]
        _ = (-y 0) * ∑ i, a i * hS (Finset.univ.image (P i)) (-fun _ => 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hS_smul_of_nonneg _ (by linarith)]
            ring
        _ = (∑ i, a i * hS (Finset.univ.image (P i)) (fun _ => 1)) * y 0 := by
            rw [hneg]
            ring
  rw [hlin]
  exact FlagAux.dot_mem_LSpan _ _

/-! ## The induction step -/

namespace CompleteAux

/-- **One direction group.**  Let `ν 0 = 1` and let `q x` (`x ∈ J`) be `n`-simplices lying in
hyperplanes `{⟨ν, ·⟩ = c x}` of `ℝ^{n+1}`.  If every flag functional `Λ_{(0, us)}` (`us` a flag of
`ℝ^n`) vanishes on `g = ∑ b_x h_{q x}`, then `g ∈ LSpan (n + 1) (n − 1)`, by the completeness in
dimension `n`. -/
theorem group_mem_LSpan {n : ℕ} (hn : 1 ≤ n) (ih : CompleteIn n) {ν : Fin (n + 1) → ℝ}
    (hν0 : ν 0 = 1) {J : Type} [Fintype J] (b : J → ℝ) (q : J → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hq : ∀ x, AffineIndependent ℝ (q x)) (c : J → ℝ) (hc : ∀ x l, dot ν (q x l) = c x)
    (hflag : ∀ us : List (Fin n → ℝ), IsFlag us →
      flagFun (us.map fun z => (Fin.cons 0 z : Fin (n + 1) → ℝ))
        (fun y => ∑ x, b x * hS (Finset.univ.image (q x)) y) = 0) :
    (fun y => ∑ x, b x * hS (Finset.univ.image (q x)) y) ∈ LSpan (n + 1) (n - 1) := by
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) → ℝ,
      G = fun z => ∑ x, b x * hS (Finset.univ.image fun l => Fin.tail (q x l)) z := ⟨_, rfl⟩
  have hGS : G ∈ SSpan n := by
    rw [hG]
    exact sum_mul_mem _ _ fun x _ => GermAux.hS_mem_SSpan (Finset.univ_nonempty.image _)
  -- the group, read in the chart
  have hdecomp : (fun y => ∑ x, b x * hS (Finset.univ.image (q x)) y) =
      (fun y => G ((chartT ν).mulVec y)) +
        dot ((∑ x, b x * c x) • (Pi.single 0 1 : Fin (n + 1) → ℝ)) := by
    funext y
    rw [hG]
    show ∑ x, b x * hS (Finset.univ.image (q x)) y =
      ∑ x, b x * hS (Finset.univ.image fun l => Fin.tail (q x l)) ((chartT ν).mulVec y) +
        dot ((∑ x, b x * c x) • (Pi.single 0 1 : Fin (n + 1) → ℝ)) y
    rw [SupportCut.dot_smul_left, dot_single_left, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hS_image_univ_eq_chartT hν0 (q x) (hc x) y]
    ring
  -- every flag functional of `ℝ^n` kills `G`
  have hGflag : ∀ us : List (Fin n → ℝ), IsFlag us → flagFun us G = 0 := by
    intro us hus
    have h := hflag us hus
    have hlen : 1 ≤ (us.map fun z => (Fin.cons 0 z : Fin (n + 1) → ℝ)).length := by
      rw [List.length_map, hus.1]
      exact hn
    rw [hdecomp, flagFun_add_dot (comp_mulVec_mem_SSpan' _ hGS) _ _ hlen,
      flagFun_comp_mulVec' _ hGS, map_cons_zero_map_chartT] at h
    exact h
  -- the induction hypothesis in the hyperplane
  have hGL : G ∈ LSpan n (n - 1) := by
    rw [hG] at hGflag ⊢
    exact ih J b (fun x l => Fin.tail (q x l)) (fun x => affineIndependent_tail hν0 (hq x) (hc x))
      hGflag
  rw [hdecomp]
  exact Submodule.add_mem _ (comp_mulVec_mem_LSpan' _ hGL) (FlagAux.dot_mem_LSpan _ _)

end CompleteAux

/-- **The induction step:** completeness in dimension `n ≥ 1` implies completeness in dimension
`n + 1`. -/
theorem completeIn_succ {n : ℕ} (hn : 1 ≤ n) (ih : CompleteIn n) : CompleteIn (n + 1) := by
  intro ι _ a P hP hflag
  have hne : ∀ i, (Finset.univ.image (P i)).Nonempty := fun i => Finset.univ_nonempty.image _
  have hfS : (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) ∈ SSpan (n + 1) :=
    sum_mul_mem _ _ fun i _ => GermAux.hS_mem_SSpan (hne i)
  -- sweep data `v = w = e₀`
  have hvw : dot (Pi.single 0 1 : Fin (n + 1) → ℝ) (Pi.single 0 1) = 1 := by
    rw [dot_single_left, Pi.single_eq_same]
  -- Step 1: the reconstruction reduces to the facet combination `g`
  obtain ⟨g, hg⟩ : ∃ g : (Fin (n + 1) → ℝ) → ℝ, g = fun y => ∑ i, a i * ∑ j,
      facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y :=
    ⟨_, rfl⟩
  have hrec : (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) -
      sweep (Pi.single 0 1) (Pi.single 0 1) g ∈ LSpan (n + 1) (n + 1 - 1) := by
    have e : (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) -
        sweep (Pi.single 0 1) (Pi.single 0 1) g =
        fun y => ∑ i, a i * (hS (Finset.univ.image (P i)) y -
          ∑ j, facetSign (P i) (hP i) (Pi.single 0 1) j *
            sweep (Pi.single 0 1) (Pi.single 0 1) (hS ((Finset.univ.erase j).image (P i))) y) := by
      rw [hg]
      funext y
      simp only [Pi.sub_apply, sweep_fun_sum, mul_sub, Finset.sum_sub_distrib]
    rw [e]
    exact sum_mul_mem _ _ fun i _ => simplex_reconstruct_any_height (P i) (hP i) _ _ hvw
  -- Step 2: `g ∈ LSpan (n + 1) (n − 1)`, one facet direction at a time
  have hgL : g ∈ LSpan (n + 1) (n - 1) := by
    have hsplit : g = fun y => ∑ ν in Finset.univ.image (fun x : ι × Fin (n + 1 + 1) =>
        facetDir (P x.1) (hP x.1) (Pi.single 0 1) x.2), ∑ i, a i * ∑ j in Finset.univ.filter
          (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
          facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y := by
      rw [hg]
      funext y
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
        (t := Finset.univ.image (fun x : ι × Fin (n + 1 + 1) =>
          facetDir (P x.1) (hP x.1) (Pi.single 0 1) x.2))
        (g := fun j => facetDir (P i) (hP i) (Pi.single 0 1) j)
        (fun j _ => Finset.mem_image_of_mem (s := Finset.univ) (a := (i, j))
          (fun x : ι × Fin (n + 1 + 1) => facetDir (P x.1) (hP x.1) (Pi.single 0 1) x.2)
          (Finset.mem_univ (i, j)))]
    rw [hsplit]
    refine sum_fun_mem _ fun ν _ => ?_
    by_cases hν : dot ν (Pi.single 0 1) = 1
    · -- a direction transverse to `e₀`
      have hν0 : ν 0 = 1 := by
        rw [← FacetGermAux.dot_single ν 0]
        exact hν
      -- the group of direction `ν`, indexed by its facets
      have hJ : (fun y => ∑ i, a i * ∑ j in Finset.univ.filter
          (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
          facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y) =
          fun y => ∑ x : {x : ι × Fin (n + 1 + 1) //
            facetDir (P x.1) (hP x.1) (Pi.single 0 1) x.2 = ν},
            (a x.1.1 * facetSign (P x.1.1) (hP x.1.1) (Pi.single 0 1) x.1.2) *
              hS (Finset.univ.image (P x.1.1 ∘ x.1.2.succAbove)) y := by
        funext y
        rw [sum_mul_sum_filter_eq_sum_subtype
          (fun i j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν)]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [FacetGermAux.image_univ_comp_succAbove, mul_assoc]
      -- the facet datum of `f` in direction `ν` is the group, modulo `LSpan (n + 1) (n − 1)`
      have hdiff : germDiff ν (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) -
          (fun y => ∑ i, a i * ∑ j in Finset.univ.filter
            (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
            facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y)
          ∈ LSpan (n + 1) (n - 1) := by
        rw [germDiff_sum_mul_hS _ _ _ hne]
        have e : (fun y => ∑ i, a i * germDiff ν (hS (Finset.univ.image (P i))) y) -
            (fun y => ∑ i, a i * ∑ j in Finset.univ.filter
              (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
              facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y) =
            fun y => ∑ i, a i * (germDiff ν (hS (Finset.univ.image (P i))) -
              ∑ j in Finset.univ.filter (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
                facetSign (P i) (hP i) (Pi.single 0 1) j •
                  hS ((Finset.univ.erase j).image (P i))) y := by
          funext y
          simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
            Finset.sum_sub_distrib]
        rw [e]
        refine sum_mul_mem _ _ fun i _ => ?_
        have h := germDiff_hS_simplex_sub_mem_LSpan (by omega : 2 ≤ n + 1) (P i) (hP i) hν
        rwa [show n + 1 - 2 = n - 1 by omega] at h
      have hgS : (fun y => ∑ i, a i * ∑ j in Finset.univ.filter
          (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
          facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y)
          ∈ SSpan (n + 1) :=
        sum_mul_mem _ _ fun i _ => sum_mul_mem _ _ fun j _ =>
          GermAux.hS_mem_SSpan (facet_nonempty (P i) j)
      -- each facet of direction `ν` lies in a hyperplane orthogonal to `ν`
      have hc : ∀ (x : {x : ι × Fin (n + 1 + 1) //
          facetDir (P x.1) (hP x.1) (Pi.single 0 1) x.2 = ν}) (l : Fin (n + 1)),
          dot ν ((P x.1.1 ∘ x.1.2.succAbove) l) = dot ν (P x.1.1 (x.1.2.succAbove 0)) := by
        intro x l
        have h := dot_facetDir_eq_of_ne (P x.1.1) (hP x.1.1) (Pi.single 0 1)
          (Fin.succAbove_ne x.1.2 l) (Fin.succAbove_ne x.1.2 0)
        rw [x.2] at h
        exact h
      rw [hJ]
      refine group_mem_LSpan (J := {x : ι × Fin (n + 1 + 1) //
          facetDir (P x.1) (hP x.1) (Pi.single 0 1) x.2 = ν}) hn ih hν0
        (fun x => a x.1.1 * facetSign (P x.1.1) (hP x.1.1) (Pi.single 0 1) x.1.2)
        (fun x => P x.1.1 ∘ x.1.2.succAbove)
        (fun x => FacetGermAux.affineIndependent_comp_succAbove (hP x.1.1) x.1.2)
        (fun x => dot ν (P x.1.1 (x.1.2.succAbove 0))) hc (fun us hus => ?_)
      · -- the flags `(0, us)` come from the flags `ν :: (0, us)` of `ℝ^{n+1}`
        have h0 := hflag _ (isFlag_cons_map_cons_zero hν0 hus)
        have hne' : (us.map fun z => (Fin.cons 0 z : Fin (n + 1) → ℝ)) ≠ [] := by
          intro h
          have hl := congrArg List.length h
          rw [List.length_map, hus.1, List.length_nil] at hl
          omega
        have hlen : n - 1 + 1 ≤ (us.map fun z => (Fin.cons 0 z : Fin (n + 1) → ℝ)).length := by
          rw [List.length_map, hus.1]
          omega
        rw [flagFun_cons _ _ hne', flagFun_eq_of_sub_mem_LSpan (germDiff_mem_SSpan hfS ν) hgS
          hdiff _ hlen, hJ] at h0
        exact h0
    · -- a direction parallel to `e₀`: the facets are vertical and carry the sign `0`
      have h0 : (fun y => ∑ i, a i * ∑ j in Finset.univ.filter
          (fun j => facetDir (P i) (hP i) (Pi.single 0 1) j = ν),
          facetSign (P i) (hP i) (Pi.single 0 1) j * hS ((Finset.univ.erase j).image (P i)) y) =
          0 := by
        funext y
        show _ = (0 : ℝ)
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Finset.sum_eq_zero, mul_zero]
        intro j hj
        rcases dot_facetDir_self_or_facetSign_eq_zero (P i) (hP i) (v := Pi.single 0 1) (j := j)
          with h | h
        · rw [(Finset.mem_filter.mp hj).2] at h
          exact absurd h hν
        · rw [h, zero_mul]
      rw [h0]
      exact Submodule.zero_mem _
  -- Step 3: the sweep raises the dimension by at most one
  have hsw := sweep_mem_LSpan hvw hgL
  rw [show n - 1 + 1 = n + 1 - 1 by omega] at hsw
  have h := Submodule.add_mem _ hrec hsw
  rwa [sub_add_cancel] at h

/-! ## The theorem -/

/-- **Completeness of the flag functionals** (blueprint M-Complete; paper Theorem 4.1, explicit
Lemma 1).  A finite combination `∑ᵢ aᵢ h_{Pᵢ}` of support functions of `m`-simplices of `ℝ^m`
(`m ≥ 1`) on which every flag functional vanishes is a combination of support functions of point
sets of affine dimension `≤ m − 1`. -/
theorem mem_LSpan_of_flagFun_eq_zero {m : ℕ} (hm : 1 ≤ m) {ι : Type} [Fintype ι] (a : ι → ℝ)
    (P : ι → Fin (m + 1) → (Fin m → ℝ)) (hP : ∀ i, AffineIndependent ℝ (P i))
    (hflag : ∀ us, IsFlag us →
      flagFun us (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) = 0) :
    (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) ∈ LSpan m (m - 1) := by
  have key : CompleteIn m :=
    Nat.le_induction (m := 1) (P := fun k _ => CompleteIn k) completeIn_one
      (fun k hk ih => completeIn_succ hk ih) m hm
  exact key ι a P hP hflag

/-- **Completeness, modulo lower-dimensional terms** (the form used downstream, after the Kuhn
decomposition).  If `f ∈ SSpan m` differs from a finite combination of support functions of
`m`-simplices by an element of `LSpan m (m − 1)`, and every flag functional of `ℝ^m` vanishes on
`f`, then `f ∈ LSpan m (m − 1)`. -/
theorem mem_LSpan_of_flagFun_eq_zero_of_sub_mem {m : ℕ} (hm : 1 ≤ m) {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ SSpan m) {ι : Type} [Fintype ι] (a : ι → ℝ)
    (P : ι → Fin (m + 1) → (Fin m → ℝ)) (hP : ∀ i, AffineIndependent ℝ (P i))
    (hsub : f - (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) ∈ LSpan m (m - 1))
    (hflag : ∀ us, IsFlag us → flagFun us f = 0) : f ∈ LSpan m (m - 1) := by
  have hgS : (fun y => ∑ i, a i * hS (Finset.univ.image (P i)) y) ∈ SSpan m :=
    sum_mul_mem _ _ fun i _ => GermAux.hS_mem_SSpan (Finset.univ_nonempty.image _)
  have hg := mem_LSpan_of_flagFun_eq_zero hm a P hP fun us hus => by
    rw [← flagFun_eq_of_sub_mem_LSpan hf hgS hsub us (by rw [hus.1]; omega)]
    exact hflag us hus
  have h := Submodule.add_mem _ hsub hg
  rwa [sub_add_cancel] at h

end

end MaxNN.ParamidGeom
