import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Scalar affine functions and H-presented polyhedra

Vocabulary bricks for the CPWL development (`MaxNN/CPWL/Def.lean`):

* `AffineFn d` — a scalar affine function on `ℝ^d` as finite data (gradient `a`,
  constant `c`), evaluating to `x ↦ (∑ j, a j * x j) + c`;
* `Polyhedron d` — a finite system of closed affine halfspace constraints;
  `Polyhedron.carrier` is the closed polyhedron it cuts out.  The data is an
  H-presentation; two different presentations may carve out the same set.

Each operation comes with its evaluation/membership lemma:

* `AffineFn.linComb` — linear combination of two affine functions;
* `Polyhedron.univ` — all of `ℝ^d` (empty constraint system);
* `Polyhedron.inter` — concatenate two constraint systems (`carrier`s intersect);
* `Polyhedron.evalLe g₁ g₂` — the comparison halfspace `{x | g₁.eval x ≤ g₂.eval x}`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- A scalar affine function on `ℝ^d`, as finite data: gradient `a` and constant `c`.
It evaluates to `x ↦ (∑ j, a j * x j) + c`; see `AffineFn.eval`. -/
structure AffineFn (d : ℕ) where
  a : Fin d → ℝ
  c : ℝ

namespace AffineFn

variable {d : ℕ}

/-- Evaluation: `g.eval x = (∑ j, g.a j * x j) + g.c`. -/
noncomputable def eval (g : AffineFn d) (x : Fin d → ℝ) : ℝ :=
  (∑ j, g.a j * x j) + g.c

/-- The linear combination `c₁ • g₁ + c₂ • g₂` of two affine functions, as data. -/
noncomputable def linComb (c₁ c₂ : ℝ) (g₁ g₂ : AffineFn d) : AffineFn d where
  a := fun j => c₁ * g₁.a j + c₂ * g₂.a j
  c := c₁ * g₁.c + c₂ * g₂.c

theorem linComb_eval (c₁ c₂ : ℝ) (g₁ g₂ : AffineFn d) (x : Fin d → ℝ) :
    (linComb c₁ c₂ g₁ g₂).eval x = c₁ * g₁.eval x + c₂ * g₂.eval x := by
  show (∑ j, (c₁ * g₁.a j + c₂ * g₂.a j) * x j) + (c₁ * g₁.c + c₂ * g₂.c)
      = c₁ * ((∑ j, g₁.a j * x j) + g₁.c) + c₂ * ((∑ j, g₂.a j * x j) + g₂.c)
  rw [Finset.sum_congr rfl fun j _ => show (c₁ * g₁.a j + c₂ * g₂.a j) * x j
        = c₁ * (g₁.a j * x j) + c₂ * (g₂.a j * x j) by ring,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end AffineFn

/-- A finite system of closed affine halfspace constraints in `ℝ^d`: `facets` many
inequalities `∑ j, C l j * x j ≤ r l`.  The closed polyhedron it cuts out is
`Polyhedron.carrier`; the data is an H-presentation of that set. -/
structure Polyhedron (d : ℕ) where
  facets : ℕ
  C : Fin facets → Fin d → ℝ
  r : Fin facets → ℝ

namespace Polyhedron

variable {d : ℕ}

/-- The closed polyhedron a constraint system cuts out. -/
def carrier (P : Polyhedron d) : Set (Fin d → ℝ) :=
  { x | ∀ l, (∑ j, P.C l j * x j) ≤ P.r l }

theorem mem_carrier {P : Polyhedron d} {x : Fin d → ℝ} :
    x ∈ P.carrier ↔ ∀ l, (∑ j, P.C l j * x j) ≤ P.r l := Iff.rfl

/-- All of `ℝ^d`, as the empty constraint system. -/
def univ (d : ℕ) : Polyhedron d :=
  ⟨0, fun l => l.elim0, fun l => l.elim0⟩

theorem mem_univ (x : Fin d → ℝ) : x ∈ (univ d).carrier := fun l => l.elim0

/-- Intersection: concatenate the two constraint systems. -/
noncomputable def inter (P Q : Polyhedron d) : Polyhedron d :=
  ⟨P.facets + Q.facets, Fin.addCases P.C Q.C, Fin.addCases P.r Q.r⟩

theorem inter_C_castAdd (P Q : Polyhedron d) (l : Fin P.facets) :
    (P.inter Q).C (Fin.castAdd Q.facets l) = P.C l := by
  show Fin.addCases (motive := fun _ => Fin d → ℝ) P.C Q.C (Fin.castAdd Q.facets l) = P.C l
  rw [Fin.addCases_left]

theorem inter_C_natAdd (P Q : Polyhedron d) (l : Fin Q.facets) :
    (P.inter Q).C (Fin.natAdd P.facets l) = Q.C l := by
  show Fin.addCases (motive := fun _ => Fin d → ℝ) P.C Q.C (Fin.natAdd P.facets l) = Q.C l
  rw [Fin.addCases_right]

theorem inter_r_castAdd (P Q : Polyhedron d) (l : Fin P.facets) :
    (P.inter Q).r (Fin.castAdd Q.facets l) = P.r l := by
  show Fin.addCases (motive := fun _ => ℝ) P.r Q.r (Fin.castAdd Q.facets l) = P.r l
  rw [Fin.addCases_left]

theorem inter_r_natAdd (P Q : Polyhedron d) (l : Fin Q.facets) :
    (P.inter Q).r (Fin.natAdd P.facets l) = Q.r l := by
  show Fin.addCases (motive := fun _ => ℝ) P.r Q.r (Fin.natAdd P.facets l) = Q.r l
  rw [Fin.addCases_right]

theorem mem_inter {P Q : Polyhedron d} {x : Fin d → ℝ} :
    x ∈ (P.inter Q).carrier ↔ x ∈ P.carrier ∧ x ∈ Q.carrier := by
  constructor
  · intro h
    constructor
    · intro l
      have hl := h (Fin.castAdd Q.facets l)
      rw [inter_C_castAdd, inter_r_castAdd] at hl
      exact hl
    · intro l
      have hl := h (Fin.natAdd P.facets l)
      rw [inter_C_natAdd, inter_r_natAdd] at hl
      exact hl
  · intro h l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · rw [inter_C_castAdd, inter_r_castAdd]
      exact h.1 l
    · rw [inter_C_natAdd, inter_r_natAdd]
      exact h.2 l

/-- The comparison halfspace `{x | g₁.eval x ≤ g₂.eval x}` of two affine functions,
as a single-constraint polyhedron. -/
noncomputable def evalLe (g₁ g₂ : AffineFn d) : Polyhedron d :=
  ⟨1, fun _ j => g₁.a j - g₂.a j, fun _ => g₂.c - g₁.c⟩

theorem mem_evalLe {g₁ g₂ : AffineFn d} {x : Fin d → ℝ} :
    x ∈ (evalLe g₁ g₂).carrier ↔ g₁.eval x ≤ g₂.eval x := by
  have key : ∀ l : Fin (evalLe g₁ g₂).facets, (∑ j, (evalLe g₁ g₂).C l j * x j)
      = (∑ j, g₁.a j * x j) - (∑ j, g₂.a j * x j) := by
    intro l
    rw [show (∑ j, (evalLe g₁ g₂).C l j * x j) = ∑ j, (g₁.a j - g₂.a j) * x j from rfl,
      Finset.sum_congr rfl fun j _ => sub_mul (g₁.a j) (g₂.a j) (x j),
      Finset.sum_sub_distrib]
  constructor
  · intro h
    have h0 := h ⟨0, Nat.zero_lt_one⟩
    rw [key ⟨0, Nat.zero_lt_one⟩] at h0
    show (∑ j, g₁.a j * x j) + g₁.c ≤ (∑ j, g₂.a j * x j) + g₂.c
    have hr : (evalLe g₁ g₂).r ⟨0, Nat.zero_lt_one⟩ = g₂.c - g₁.c := rfl
    rw [hr] at h0
    linarith
  · intro h l
    rw [key l]
    have hg : (∑ j, g₁.a j * x j) + g₁.c ≤ (∑ j, g₂.a j * x j) + g₂.c := h
    have hr : (evalLe g₁ g₂).r l = g₂.c - g₁.c := rfl
    rw [hr]
    linarith

end Polyhedron

end MaxNN
