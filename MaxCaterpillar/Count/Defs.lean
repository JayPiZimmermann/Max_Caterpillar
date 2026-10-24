import MaxCaterpillar.Count.TreeFace

/-!
# Definitions for the exponential count

* `IsMixedExpansion r K₁ K₂`: `max_N` (`N = r + 2`) is a linear combination of the
  caterpillar functions of `K₁`, the tree face functions of `K₂` (`Count/TreeFace.lean`),
  and the auxiliary functions.
* `OmegaLe D Δ`: every vertex `v` of the hinge forest of `D` has `ω(v) ≤ Δ`, where `ω(v)`
  (`trunkDeg`) counts the out-leaves adjacent to `v` (leaves with `κ = 1`) plus one if `v`
  has a neighbour of degree `≥ 2`.
* `IsBrunckExpansion`: `IsMixedExpansion` with every tree unit a face of a rooted star of
  Brunck et al. (`TreeFace.IsStarFace`).
* `TreeFace.hingeDeg`, `OutLeafBound`: the two special classes of the corollaries.
-/

open BigOperators Finset

namespace MaxCaterpillar.Trees

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower

variable {N : ℕ}

/-- `(o, x)` or `(x, o)` is a pair of `D`. -/
def DAdj (D : Descr N) (o x : Fin N) : Prop := (o, x) ∈ D.M ∨ (x, o) ∈ D.M

/-- `κ_o = h_o + #{(o, x) ∈ M}`. -/
noncomputable def DKappa (D : Descr N) (o : Fin N) : ℝ :=
  (D.h o : ℝ) + ((D.M.filter fun m => m.1 = o).card : ℝ)

/-- The pairs of `E` incident with `o`. -/
def incid {N : ℕ} (E : Finset (Fin N × Fin N)) (o : Fin N) : Finset (Fin N × Fin N) :=
  E.filter fun m => m.1 = o ∨ m.2 = o

namespace TreeFace

variable (F : TreeFace N)

/-- The hinge degree of `u`: the number of hinge edges of the tree at `u`. -/
noncomputable def hingeDeg (u : Fin N) : ℕ := by
  classical
  exact (F.edgeVerts.filter fun v => F.state v = .hinge ∧ (v = u ∨ F.parent v = u)).card

/-- The faces of the rooted-star pyramids of Brunck et al.: every edge joins a leaf to the
root `c` and carries `x_c - x_l` (omitted, linear, or as the hinge `σ(x_c - x_l)`). -/
def IsStarFace : Prop := ∀ v ∈ F.edgeVerts, F.parent v = F.root ∧ F.up v = true

/-- Caterpillar trees whose leaves carry `x_parent - x_leaf`: a spine `P` containing the root,
closed under `parent`, a path (no two spine vertices share a parent), every other vertex
except the apex a leaf of the spine with `up = true`. -/
def IsUpCaterpillar : Prop :=
  ∃ P : Finset (Fin N), F.root ∈ P ∧ F.apex ∉ P ∧
    (∀ v ∈ P, v ≠ F.root → F.parent v ∈ P) ∧
    (∀ u ∈ P, ∀ v ∈ P, u ≠ F.root → v ≠ F.root → F.parent u = F.parent v → u = v) ∧
    (∀ v, v ∉ P → v ≠ F.apex → F.parent v ∈ P ∧ F.up v = true)

end TreeFace

/-- `K₁` (caterpillar face descriptions) and `K₂` (tree face descriptions) form an
expansion of `max_N`: `max_N = Σ_{K₁} d₁ U + Σ_{K₂} d₂ U + (auxiliary)`. -/
def IsMixedExpansion (r : ℕ) (K₁ : Finset (FaceKey r)) (K₂ : Finset (TreeFace (r + 1 + 1))) :
    Prop :=
  K₁ ⊆ caterpillarDescriptions r ∧
    ∃ (d₁ : FaceKey r → ℝ) (d₂ : TreeFace (r + 1 + 1) → ℝ)
      (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in K₁, d₁ k * caterpillarFunction k x + ∑ F in K₂, d₂ F * F.unit x +
          ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

end MaxCaterpillar.Trees

namespace MaxCaterpillar.Count

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountLower Trees

section Class

open Classical

variable {N : ℕ}

/-- The hinge neighbours of `v`. -/
noncomputable def nbrs (D : Descr N) (v : Fin N) : Finset (Fin N) := univ.filter (DAdj D v)

/-- An out-leaf: one hinge neighbour and `κ = 1`. -/
def IsOLeaf (D : Descr N) (u : Fin N) : Prop := (nbrs D u).card = 1 ∧ DKappa D u = 1

/-- `ω(v)`: the out-leaves adjacent to `v`, plus one if `v` has a neighbour of degree `≥ 2`. -/
noncomputable def trunkDeg (D : Descr N) (v : Fin N) : ℕ :=
  (univ.filter fun u => DAdj D v u ∧ IsOLeaf D u).card +
    if ∃ w, DAdj D v w ∧ 1 < (nbrs D w).card then 1 else 0

/-- **The class**: `ω(v) ≤ Δ` at every vertex. -/
def OmegaLe (D : Descr N) (Δ : ℕ) : Prop := ∀ v, trunkDeg D v ≤ Δ

/-- `u` is an *out-leaf* of `D`: it lies on exactly one pair and `κ_u = 1`. -/
def IsOutLeaf (D : Descr N) (u : Fin N) : Prop :=
  (incid D.M u).card = 1 ∧ DKappa D u = 1

/-- Every vertex is adjacent to at most `s` out-leaves. -/
def OutLeafBound (D : Descr N) (s : ℕ) : Prop :=
  ∀ v (U : Finset (Fin N)), (∀ u ∈ U, DAdj D v u ∧ IsOutLeaf D u) → U.card ≤ s

end Class

/-- An expansion of `max_N` by caterpillar functions (`K₁`) and rooted-star faces (`K₂`). -/
def IsBrunckExpansion (r : ℕ) (K₁ : Finset (FaceKey r)) (K₂ : Finset (TreeFace (r + 1 + 1))) :
    Prop :=
  K₁ ⊆ caterpillarDescriptions r ∧ (∀ F ∈ K₂, TreeFace.IsStarFace F) ∧
    ∃ (d₁ : FaceKey r → ℝ) (d₂ : TreeFace (r + 1 + 1) → ℝ)
      (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ),
      ∀ x, Maximum (r + 1 + 1) x =
        ∑ k in K₁, d₁ k * caterpillarFunction k x + ∑ F in K₂, d₂ F * F.unit x +
          ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x

end MaxCaterpillar.Count
