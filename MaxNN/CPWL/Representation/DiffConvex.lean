import MaxNN.CPWL.Representation.DiffConvex.OneDim.Core
import MaxNN.CPWL.Representation.DiffConvex.LineData
import MaxNN.CPWL.Representation.ConvexMax
import MaxNN.CPWL.Networks

/-!
# Every CPWL function is a difference of two convex CPWL functions

Stage (i) of the hinging-representation programme, and its corollary chain.

`diffConvex_of_mem_cpwl`: for `f ∈ CPWL d` with witness pieces `g i`, the
**convexifier** `q := ∑ (i,j), relu (g i - g j)` (sum over all ordered pairs of the
witness's affine functions) satisfies:

* `q` is convex and CPWL — hence a maximum of finitely many affine functions;
* `f + q` is convex and CPWL — convexity is checked **along every line**, where the
  one-dimensional core (`OneDim/Core.lean`) applies: the restriction of the witness to
  a line is a finite closed interval cover, and each concave kink of `f` along the
  line sits at a crossing point of the two active affine pieces, where the pair sum
  gains at least the kink back.

Corollaries:

* `exists_convex_cpwl_decomposition` — the classical difference-of-convex statement;
* `exists_mem_reluClass_of_mem_cpwl` — every CPWL function is computed exactly by a
  ReLU network of some depth;
* `cpwl_eq_iUnion_reluClass` — **`CPWL d = ⋃ k, ReLUClass d k`**: continuous
  piecewise-linear functions are exactly the ReLU-computable functions.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- **Difference-of-convex decomposition** (stage (i) of the representation
programme): every CPWL function is a difference of two maxima of finitely many affine
functions. -/
theorem diffConvex_of_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : f ∈ CPWL d) :
    ∃ p q : (Fin d → ℝ) → ℝ, IsMaxOfAffine d p ∧ IsMaxOfAffine d q ∧
      ∀ x, f x = p x - q x := by
  have hfc : Continuous f := hf.1
  obtain ⟨W⟩ := hf.2
  obtain ⟨n, P, g, covers, agrees⟩ := W
  -- the convexifier: sum of relus of all ordered pairwise differences
  have hterm_cpwl : ∀ p : Fin n × Fin n,
      (fun z => relu ((g p.1).eval z - (g p.2).eval z)) ∈ CPWL d := fun p =>
    max_mem_cpwl (const_mem_cpwl 0)
      (sub_mem_cpwl (affineFn_mem_cpwl (g p.1)) (affineFn_mem_cpwl (g p.2)))
  have hq_cpwl : (fun z : Fin d → ℝ => ∑ p : Fin n × Fin n,
      relu ((g p.1).eval z - (g p.2).eval z)) ∈ CPWL d :=
    sum_mem_cpwl Finset.univ _ fun p _ => hterm_cpwl p
  have hterm_convex : ∀ p : Fin n × Fin n, ConvexOn ℝ Set.univ
      (fun z : Fin d → ℝ => relu ((g p.1).eval z - (g p.2).eval z)) := by
    intro p
    have he : (AffineFn.linComb 1 (-1) (g p.1) (g p.2)).eval
        = fun z => (g p.1).eval z - (g p.2).eval z := by
      funext z
      rw [AffineFn.linComb_eval]
      ring
    have hΔ := (AffineFn.linComb 1 (-1) (g p.1) (g p.2)).convexOn_eval
    rw [he] at hΔ
    exact ConvexOn.sup (convexOn_const 0 convex_univ) hΔ
  have hq_convex : ConvexOn ℝ Set.univ (fun z : Fin d → ℝ => ∑ p : Fin n × Fin n,
      relu ((g p.1).eval z - (g p.2).eval z)) :=
    convexOn_finset_sum convex_univ Finset.univ _ fun p _ => hterm_convex p
  -- the sum `f + q` is convex: check along every line via the 1-D core
  have hp_convex : ConvexOn ℝ Set.univ (fun z => f z + ∑ p : Fin n × Fin n,
      relu ((g p.1).eval z - (g p.2).eval z)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hpathcont : Continuous fun t : ℝ => x + t • (y - x) := by
      refine continuous_pi fun j => ?_
      show Continuous fun t : ℝ => x j + t * (y j - x j)
      exact continuous_const.add (continuous_id.mul continuous_const)
    have hcore := convexOn_pl_add_reluPairs
      (fun i => {t : ℝ | (x + t • (y - x)) ∈ (P i).carrier})
      (fun i => ∑ j, (g i).a j * (y - x) j) (fun i => (g i).eval x)
      (fun t => f (x + t • (y - x)))
      (hfc.comp hpathcont)
      (fun i => (P i).isClosed_line_preimage x (y - x))
      (fun i => (P i).convex_line_preimage x (y - x))
      (fun t => covers (x + t • (y - x)))
      (fun i t hti => by
        show f (x + t • (y - x))
            = (∑ j, (g i).a j * (y - x) j) * t + (g i).eval x
        rw [agrees i _ hti, AffineFn.eval_line])
    have happ := hcore.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
    rw [show (a : ℝ) • (0 : ℝ) + b • (1 : ℝ) = b from by
      rw [smul_eq_mul, smul_eq_mul]; ring] at happ
    have happ' : f (x + b • (y - x)) + (∑ p : Fin n × Fin n,
        relu (((∑ j, (g p.1).a j * (y - x) j) * b + (g p.1).eval x)
          - ((∑ j, (g p.2).a j * (y - x) j) * b + (g p.2).eval x)))
        ≤ a * (f (x + (0 : ℝ) • (y - x)) + ∑ p : Fin n × Fin n,
          relu (((∑ j, (g p.1).a j * (y - x) j) * 0 + (g p.1).eval x)
            - ((∑ j, (g p.2).a j * (y - x) j) * 0 + (g p.2).eval x)))
        + b * (f (x + (1 : ℝ) • (y - x)) + ∑ p : Fin n × Fin n,
          relu (((∑ j, (g p.1).a j * (y - x) j) * 1 + (g p.1).eval x)
            - ((∑ j, (g p.2).a j * (y - x) j) * 1 + (g p.2).eval x))) := happ
    -- convert the three evaluation points into the target vocabulary
    have hb' : x + b • (y - x) = a • x + b • y := (line_convex_combo x y hab).symm
    have hev_b : ∀ i : Fin n, (∑ j, (g i).a j * (y - x) j) * b + (g i).eval x
        = (g i).eval (a • x + b • y) := by
      intro i
      rw [← AffineFn.eval_line, hb']
    have hev_0 : ∀ i : Fin n, (∑ j, (g i).a j * (y - x) j) * 0 + (g i).eval x
        = (g i).eval x := by
      intro i
      rw [mul_zero, zero_add]
    have hev_1 : ∀ i : Fin n, (∑ j, (g i).a j * (y - x) j) * 1 + (g i).eval x
        = (g i).eval y := by
      intro i
      rw [← AffineFn.eval_line, line_at_one]
    have hs_b : (∑ p : Fin n × Fin n,
        relu (((∑ j, (g p.1).a j * (y - x) j) * b + (g p.1).eval x)
          - ((∑ j, (g p.2).a j * (y - x) j) * b + (g p.2).eval x)))
        = ∑ p : Fin n × Fin n,
          relu ((g p.1).eval (a • x + b • y) - (g p.2).eval (a • x + b • y)) :=
      Finset.sum_congr rfl fun p _ => by rw [hev_b p.1, hev_b p.2]
    have hs_0 : (∑ p : Fin n × Fin n,
        relu (((∑ j, (g p.1).a j * (y - x) j) * 0 + (g p.1).eval x)
          - ((∑ j, (g p.2).a j * (y - x) j) * 0 + (g p.2).eval x)))
        = ∑ p : Fin n × Fin n, relu ((g p.1).eval x - (g p.2).eval x) :=
      Finset.sum_congr rfl fun p _ => by rw [hev_0 p.1, hev_0 p.2]
    have hs_1 : (∑ p : Fin n × Fin n,
        relu (((∑ j, (g p.1).a j * (y - x) j) * 1 + (g p.1).eval x)
          - ((∑ j, (g p.2).a j * (y - x) j) * 1 + (g p.2).eval x)))
        = ∑ p : Fin n × Fin n, relu ((g p.1).eval y - (g p.2).eval y) :=
      Finset.sum_congr rfl fun p _ => by rw [hev_1 p.1, hev_1 p.2]
    rw [hs_b, hs_0, hs_1, hb', line_at_zero, line_at_one] at happ'
    show f (a • x + b • y) + (∑ p : Fin n × Fin n,
        relu ((g p.1).eval (a • x + b • y) - (g p.2).eval (a • x + b • y)))
      ≤ a * (f x + ∑ p : Fin n × Fin n, relu ((g p.1).eval x - (g p.2).eval x))
        + b * (f y + ∑ p : Fin n × Fin n, relu ((g p.1).eval y - (g p.2).eval y))
    exact happ'
  have hp_cpwl : (fun z => f z + ∑ p : Fin n × Fin n,
      relu ((g p.1).eval z - (g p.2).eval z)) ∈ CPWL d :=
    add_mem_cpwl hf hq_cpwl
  exact ⟨_, _, isMaxOfAffine_of_convexOn_cpwl hp_cpwl hp_convex,
    isMaxOfAffine_of_convexOn_cpwl hq_cpwl hq_convex, fun x => by ring⟩

/-- The classical difference-of-convex statement: every CPWL function is a difference
of two **convex CPWL** functions. -/
theorem exists_convex_cpwl_decomposition {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) :
    ∃ p q : (Fin d → ℝ) → ℝ, p ∈ CPWL d ∧ q ∈ CPWL d ∧
      ConvexOn ℝ Set.univ p ∧ ConvexOn ℝ Set.univ q ∧ ∀ x, f x = p x - q x := by
  obtain ⟨p, q, hp, hq, hpq⟩ := diffConvex_of_mem_cpwl hf
  exact ⟨p, q, mem_cpwl_of_isMaxOfAffine hp, mem_cpwl_of_isMaxOfAffine hq,
    convexOn_of_isMaxOfAffine hp, convexOn_of_isMaxOfAffine hq, hpq⟩

/-- **Every CPWL function is computed exactly by some ReLU network.** -/
theorem exists_mem_reluClass_of_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) : ∃ k, f ∈ ReLUClass d k := by
  obtain ⟨p, q, hp, hq, hpq⟩ := diffConvex_of_mem_cpwl hf
  obtain ⟨kp, hkp⟩ := exists_mem_reluClass_of_isMaxOfAffine hp
  obtain ⟨kq, hkq⟩ := exists_mem_reluClass_of_isMaxOfAffine hq
  refine ⟨max kp kq, ?_⟩
  have h := sub_mem_reluClass (reluClass_mono (le_max_left kp kq) hkp)
    (reluClass_mono (le_max_right kp kq) hkq)
  have e : (fun x => p x - q x) = f := funext fun x => (hpq x).symm
  rw [e] at h
  exact h

/-- **`CPWL d = ⋃ k, ReLUClass d k`**: the continuous piecewise-linear functions are
exactly the functions computed by ReLU networks (of some finite depth). -/
theorem cpwl_eq_iUnion_reluClass (d : ℕ) : CPWL d = ⋃ k, ReLUClass d k := by
  ext f
  constructor
  · intro hf
    obtain ⟨k, hk⟩ := exists_mem_reluClass_of_mem_cpwl hf
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  · intro hf
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hf
    exact reluClass_subset_cpwl d k hk

end MaxNN
