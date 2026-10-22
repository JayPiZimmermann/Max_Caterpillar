import MaxNN.CPWL.Pieces.Polyhedra
import MaxNN.CPWL.Pieces.Topology
import MaxNN.Core.Affine
import Mathlib.Data.Fintype.Card

/-!
# `CPWL d` — continuous piecewise-linear functions on `ℝ^d`

`CPWL d` is the class of scalar functions on `ℝ^d` that are continuous and admit a
**finite** closed polyhedral cover of `ℝ^d` on each piece of which the function agrees
with an affine function (`CPWLWitness`).  This is the honest textbook definition:

* finiteness is explicit — a witness consists of `n` pieces, each an H-presented
  polyhedron with finitely many facets (`Polyhedron`), and `n` affine functions;
* the pieces must **cover** `ℝ^d` (`covers`), so a witness cannot be vacuous — in
  particular `n = 0` is impossible;
* the definition is NOT the (strictly weaker for the cover-free reading) "`f x` lies
  pointwise in the values of finitely many affine functions" — the agreement is on the
  pieces of an actual polyhedral cover.

Continuity is stated as an explicit conjunct.  (For a genuine witness it is in fact
automatic by the pasting lemma for finite closed covers, but we do not rely on that.)

Base membership lemmas: `affineFn_mem_cpwl`, `affine_mem_cpwl`, `const_mem_cpwl`,
`coord_mem_cpwl`.  Closure lemmas are in `MaxNN/CPWL/Closure.lean`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- A witness that `f` is piecewise-linear: finitely many closed H-presented polyhedral
pieces covering `ℝ^d`, and on each piece `f` agrees with an affine function. -/
structure CPWLWitness (d : ℕ) (f : (Fin d → ℝ) → ℝ) where
  /-- The number of polyhedral pieces. -/
  n : ℕ
  /-- The closed polyhedral pieces (H-presentations). -/
  P : Fin n → Polyhedron d
  /-- The affine function attached to each piece. -/
  g : Fin n → AffineFn d
  /-- The pieces cover `ℝ^d`. -/
  covers : ∀ x, ∃ i, x ∈ (P i).carrier
  /-- On each piece, `f` agrees with the attached affine function. -/
  agrees : ∀ i, ∀ x ∈ (P i).carrier, f x = (g i).eval x

/-- `CPWL d` (the literature's `CPWL_d`): the continuous piecewise-linear scalar
functions on `ℝ^d` — continuous, and agreeing with one of finitely many affine
functions on each piece of a finite closed polyhedral cover of `ℝ^d`. -/
def CPWL (d : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  { f | Continuous f ∧ Nonempty (CPWLWitness d f) }

theorem mem_cpwl_iff {d : ℕ} {f : (Fin d → ℝ) → ℝ} :
    f ∈ CPWL d ↔ Continuous f ∧ Nonempty (CPWLWitness d f) := Iff.rfl

/-- A CPWL function is continuous. -/
theorem continuous_of_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : f ∈ CPWL d) :
    Continuous f := hf.1

/-- Package a piecewise description indexed by an arbitrary finite type into a
`CPWLWitness` (whose pieces are `Fin`-indexed), by transporting along
`Fintype.equivFin`.  This is how the closure lemmas build their witnesses from
product and sum index types. -/
noncomputable def CPWLWitness.ofFintype {d : ℕ} {f : (Fin d → ℝ) → ℝ} {ι : Type}
    [Fintype ι] (P : ι → Polyhedron d) (g : ι → AffineFn d)
    (covers : ∀ x, ∃ i, x ∈ (P i).carrier)
    (agrees : ∀ i, ∀ x ∈ (P i).carrier, f x = (g i).eval x) : CPWLWitness d f where
  n := Fintype.card ι
  P := fun i => P ((Fintype.equivFin ι).symm i)
  g := fun i => g ((Fintype.equivFin ι).symm i)
  covers := fun x => by
    obtain ⟨i, hi⟩ := covers x
    refine ⟨Fintype.equivFin ι i, ?_⟩
    show x ∈ (P ((Fintype.equivFin ι).symm (Fintype.equivFin ι i))).carrier
    rw [Equiv.symm_apply_apply]
    exact hi
  agrees := fun i x hx => agrees ((Fintype.equivFin ι).symm i) x hx

/-! ## Base cases -/

/-- Affine functions (bundled form) are CPWL: one piece, no constraints. -/
theorem affineFn_mem_cpwl {d : ℕ} (g : AffineFn d) : g.eval ∈ CPWL d :=
  ⟨g.continuous_eval,
    ⟨⟨1, fun _ => Polyhedron.univ d, fun _ => g,
      fun x => ⟨0, Polyhedron.mem_univ x⟩, fun _ _ _ => rfl⟩⟩⟩

/-- Affine functions are CPWL. -/
theorem affine_mem_cpwl {d : ℕ} (a : Fin d → ℝ) (c : ℝ) :
    (fun x => (∑ j, a j * x j) + c) ∈ CPWL d :=
  affineFn_mem_cpwl ⟨a, c⟩

/-- Constant functions are CPWL. -/
theorem const_mem_cpwl {d : ℕ} (c : ℝ) : (fun _ : Fin d → ℝ => c) ∈ CPWL d := by
  have h := affine_mem_cpwl (fun _ : Fin d => (0 : ℝ)) c
  have e : (fun x : Fin d → ℝ => (∑ j, (0 : ℝ) * x j) + c) = fun _ => c := by
    funext x
    rw [Finset.sum_congr rfl fun j _ => zero_mul (x j), Finset.sum_const_zero, zero_add]
  rw [e] at h
  exact h

/-- Coordinate functions are CPWL. -/
theorem coord_mem_cpwl {d : ℕ} (i : Fin d) : (fun x => x i) ∈ CPWL d := by
  have h := affine_mem_cpwl (fun j => if j = i then (1 : ℝ) else 0) 0
  have e : (fun x : Fin d → ℝ => (∑ j, (if j = i then (1 : ℝ) else 0) * x j) + 0)
      = fun x => x i := by
    funext x
    rw [Affine.delta_row_sum i x, add_zero]
  rw [e] at h
  exact h

end MaxNN
