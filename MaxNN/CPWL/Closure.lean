import MaxNN.CPWL.Def
import Mathlib.Topology.Order.Basic

/-!
# Closure properties of `CPWL d`

The workhorse lemmas of the CPWL development:

* `linComb_mem_cpwl` (with `add`/`smul`/`neg`/`sub`/`sum` corollaries) — `CPWL d` is a
  vector space; the witness for a linear combination lives on the common refinement of
  the two polyhedral covers;
* `max_mem_cpwl`, `min_mem_cpwl` — `CPWL d` is a lattice; the refined pieces are split
  once more by the comparison halfspace `{x | g₁ ≤ g₂}` of the two active affine
  functions;
* `affineComb_mem_cpwl` — an affine combination `x ↦ (∑ l, coef l * v l x) + b` of CPWL
  functions is CPWL (this is how an affine network layer acts on CPWL inputs, see
  `MaxNN/CPWL/Networks.lean`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-! ## The vector-space structure -/

/-- **`CPWL d` is closed under linear combinations.**  The witness lives on the common
refinement of the two covers, with the linearly combined affine functions. -/
theorem linComb_mem_cpwl {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (c₁ c₂ : ℝ)
    (hf : f ∈ CPWL d) (hg : g ∈ CPWL d) :
    (fun x => c₁ * f x + c₂ * g x) ∈ CPWL d := by
  obtain ⟨hfc, ⟨Wf⟩⟩ := hf
  obtain ⟨hgc, ⟨Wg⟩⟩ := hg
  refine ⟨(continuous_const.mul hfc).add (continuous_const.mul hgc),
    ⟨CPWLWitness.ofFintype (ι := Fin Wf.n × Fin Wg.n)
      (fun p => (Wf.P p.1).inter (Wg.P p.2))
      (fun p => AffineFn.linComb c₁ c₂ (Wf.g p.1) (Wg.g p.2)) ?_ ?_⟩⟩
  · intro x
    obtain ⟨i₁, h₁⟩ := Wf.covers x
    obtain ⟨i₂, h₂⟩ := Wg.covers x
    exact ⟨(i₁, i₂), Polyhedron.mem_inter.mpr ⟨h₁, h₂⟩⟩
  · rintro ⟨i₁, i₂⟩ x hx
    obtain ⟨h₁, h₂⟩ := Polyhedron.mem_inter.mp hx
    show c₁ * f x + c₂ * g x = (AffineFn.linComb c₁ c₂ (Wf.g i₁) (Wg.g i₂)).eval x
    rw [AffineFn.linComb_eval, Wf.agrees i₁ x h₁, Wg.agrees i₂ x h₂]

theorem add_mem_cpwl {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) (hg : g ∈ CPWL d) : (fun x => f x + g x) ∈ CPWL d := by
  have h := linComb_mem_cpwl 1 1 hf hg
  have e : (fun x => (1 : ℝ) * f x + 1 * g x) = fun x => f x + g x := by
    funext x
    rw [one_mul, one_mul]
  rw [e] at h
  exact h

theorem smul_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ} (c : ℝ)
    (hf : f ∈ CPWL d) : (fun x => c * f x) ∈ CPWL d := by
  have h := linComb_mem_cpwl c 0 hf hf
  have e : (fun x => c * f x + 0 * f x) = fun x => c * f x := by
    funext x
    rw [zero_mul, add_zero]
  rw [e] at h
  exact h

theorem neg_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) : (fun x => -(f x)) ∈ CPWL d := by
  have h := smul_mem_cpwl (-1) hf
  have e : (fun x => (-1 : ℝ) * f x) = fun x => -(f x) := by
    funext x
    rw [neg_one_mul]
  rw [e] at h
  exact h

theorem sub_mem_cpwl {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) (hg : g ∈ CPWL d) : (fun x => f x - g x) ∈ CPWL d := by
  have h := linComb_mem_cpwl 1 (-1) hf hg
  have e : (fun x => (1 : ℝ) * f x + (-1) * g x) = fun x => f x - g x := by
    funext x
    rw [one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [e] at h
  exact h

/-- Closure under finite sums. -/
theorem sum_mem_cpwl {ι : Type _} [DecidableEq ι] {d : ℕ} (s : Finset ι)
    (F : ι → (Fin d → ℝ) → ℝ) (hF : ∀ i ∈ s, F i ∈ CPWL d) :
    (fun x => ∑ i in s, F i x) ∈ CPWL d := by
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x : Fin d → ℝ => ∑ i in (∅ : Finset ι), F i x) = fun _ => (0 : ℝ) := by
      funext x
      exact Finset.sum_empty
    rw [e]
    exact const_mem_cpwl 0
  · intro a s ha ih hF
    have e : (fun x : Fin d → ℝ => ∑ i in insert a s, F i x)
        = fun x => F a x + ∑ i in s, F i x := by
      funext x
      exact Finset.sum_insert ha
    rw [e]
    exact add_mem_cpwl (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- An affine combination `x ↦ (∑ l, coef l * v l x) + b` of CPWL functions is CPWL. -/
theorem affineComb_mem_cpwl {d m : ℕ} (coef : Fin m → ℝ) (b : ℝ)
    {v : Fin m → (Fin d → ℝ) → ℝ} (hv : ∀ l, v l ∈ CPWL d) :
    (fun x => (∑ l, coef l * v l x) + b) ∈ CPWL d := by
  have hs : (fun x : Fin d → ℝ => ∑ l, coef l * v l x) ∈ CPWL d :=
    sum_mem_cpwl Finset.univ (fun l => fun x => coef l * v l x)
      (fun l _ => smul_mem_cpwl (coef l) (hv l))
  exact add_mem_cpwl hs (const_mem_cpwl b)

/-! ## The lattice structure -/

/-- **`CPWL d` is closed under pointwise `max`.**  Each pair of refined pieces is split
by the comparison halfspace of its two active affine functions; on each half the
maximum agrees with one of them. -/
theorem max_mem_cpwl {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) (hg : g ∈ CPWL d) :
    (fun x => max (f x) (g x)) ∈ CPWL d := by
  obtain ⟨hfc, ⟨Wf⟩⟩ := hf
  obtain ⟨hgc, ⟨Wg⟩⟩ := hg
  refine ⟨hfc.max hgc,
    ⟨CPWLWitness.ofFintype (ι := (Fin Wf.n × Fin Wg.n) ⊕ (Fin Wf.n × Fin Wg.n))
      (Sum.elim
        (fun p => ((Wf.P p.1).inter (Wg.P p.2)).inter
          (Polyhedron.evalLe (Wf.g p.1) (Wg.g p.2)))
        (fun p => ((Wf.P p.1).inter (Wg.P p.2)).inter
          (Polyhedron.evalLe (Wg.g p.2) (Wf.g p.1))))
      (Sum.elim (fun p => Wg.g p.2) (fun p => Wf.g p.1)) ?_ ?_⟩⟩
  · intro x
    obtain ⟨i₁, h₁⟩ := Wf.covers x
    obtain ⟨i₂, h₂⟩ := Wg.covers x
    rcases le_total ((Wf.g i₁).eval x) ((Wg.g i₂).eval x) with hle | hle
    · exact ⟨Sum.inl (i₁, i₂), Polyhedron.mem_inter.mpr
        ⟨Polyhedron.mem_inter.mpr ⟨h₁, h₂⟩, Polyhedron.mem_evalLe.mpr hle⟩⟩
    · exact ⟨Sum.inr (i₁, i₂), Polyhedron.mem_inter.mpr
        ⟨Polyhedron.mem_inter.mpr ⟨h₁, h₂⟩, Polyhedron.mem_evalLe.mpr hle⟩⟩
  · rintro (⟨i₁, i₂⟩ | ⟨i₁, i₂⟩) x hx
    · obtain ⟨h12, h3⟩ := Polyhedron.mem_inter.mp hx
      obtain ⟨h₁, h₂⟩ := Polyhedron.mem_inter.mp h12
      show max (f x) (g x) = (Wg.g i₂).eval x
      rw [Wf.agrees i₁ x h₁, Wg.agrees i₂ x h₂]
      exact max_eq_right (Polyhedron.mem_evalLe.mp h3)
    · obtain ⟨h12, h3⟩ := Polyhedron.mem_inter.mp hx
      obtain ⟨h₁, h₂⟩ := Polyhedron.mem_inter.mp h12
      show max (f x) (g x) = (Wf.g i₁).eval x
      rw [Wf.agrees i₁ x h₁, Wg.agrees i₂ x h₂]
      exact max_eq_left (Polyhedron.mem_evalLe.mp h3)

/-- `CPWL d` is closed under pointwise `min`, via `min a b = -max (-a) (-b)`. -/
theorem min_mem_cpwl {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) (hg : g ∈ CPWL d) :
    (fun x => min (f x) (g x)) ∈ CPWL d := by
  have h : (fun x => -max (-(f x)) (-(g x))) ∈ CPWL d :=
    neg_mem_cpwl (max_mem_cpwl (neg_mem_cpwl hf) (neg_mem_cpwl hg))
  have e : (fun x => -max (-(f x)) (-(g x))) = fun x => min (f x) (g x) := by
    funext x
    rw [max_neg_neg, neg_neg]
  rw [e] at h
  exact h

end MaxNN
