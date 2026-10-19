import MaxNN.Constructions.Paramid.LowerDim
import MaxNN.Constructions.Paramid.Chain.Root
import Mathlib.Topology.Instances.Real
import Mathlib.Order.Filter.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Data.Sign

/-!
# Core definitions for the geometric half of the depth-two theorem

Shared vocabulary for `MaxNN/Constructions/Paramid/Geom/*`.  Every module of the geometric
formalization imports this file and uses exactly these names.

* `hS S` — support function `y ↦ max_{p ∈ S} ⟨p, y⟩` of a finite point set (`0` if `S = ∅`).
* `SSpan m` — the ℝ-span of support functions of nonempty finite point sets in `ℝ^m`.
* `LSpan m k` — the ℝ-span of `LowerDimSupport m k`: support functions of point sets of
  affine dimension `≤ k` (`MaxNN/Constructions/Paramid/LowerDim.lean`).
* `face u S` — the points of `S` maximizing `⟨u, ·⟩`.
* `germ f u y` — the one-sided directional derivative `lim_{t → 0+} (f (u + t y) − f u) / t`
  (a total function via `limUnder`; meaningful when the limit exists).
* `germDiff u f = germ f u − germ f (−u)` — the facet datum of `f` in direction `u`.
* `iterGermDiff [u₁, …, u_r] f = germDiff u_r (… (germDiff u₁ f))` — first element first.
* `flagFun us f = iterGermDiff us f (last us)` — the flag functional `Λ_{us}`.
* `toR`, `labelVecs`, `orient`, `rho` — the geometric realization of the lattice chains of
  `MaxNN/Constructions/Paramid/Chain.lean`: a basis chain `[γ; L]` of top degree `n − 1` in
  `Chain n` is realized as `orient γ L • paramidUnit γ (labels of L)`, where `orient γ L` is the
  sign of `det [v₁, …, v_{n−1}, γ]` (labels in increasing root order, then `γ`); generators of
  any other degree are realized as `0`.

No theorems of substance live here; see the module map in
`work/depth2_simplex/lean_core/BLUEPRINT.md`.
-/

namespace MaxNN.ParamidGeom

open BigOperators MaxNN.ParamidChain

noncomputable section

/-! ## Support functions and spans -/

/-- Support function of a finite point set, `0` on the empty set. -/
def hS {m : ℕ} (S : Finset (Fin m → ℝ)) (y : Fin m → ℝ) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun p => dot p y) else 0

theorem hS_of_nonempty {m : ℕ} {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (y : Fin m → ℝ) :
    hS S y = S.sup' h (fun p => dot p y) := by
  unfold hS
  rw [dif_pos h]

/-- The ℝ-span of support functions of nonempty finite point sets in `ℝ^m`. -/
def SSpan (m : ℕ) : Submodule ℝ ((Fin m → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ S : Finset (Fin m → ℝ), S.Nonempty ∧ f = hS S}

/-- The ℝ-span of support functions of point sets of affine dimension at most `k`. -/
def LSpan (m k : ℕ) : Submodule ℝ ((Fin m → ℝ) → ℝ) :=
  Submodule.span ℝ (LowerDimSupport m k)

/-! ## Faces -/

/-- The face of `S` in direction `u`: the points of `S` maximizing `⟨u, ·⟩`. -/
def face {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m → ℝ)) : Finset (Fin m → ℝ) :=
  @Finset.filter _ (fun p => ∀ q ∈ S, dot u q ≤ dot u p) (Classical.decPred _) S

/-! ## Germs and flag functionals -/

/-- One-sided directional derivative of `f` at `u` in direction `y`:
`lim_{t → 0+} (f (u + t • y) − f u) / t` (via `limUnder`). -/
def germ {m : ℕ} (f : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) (y : Fin m → ℝ) : ℝ :=
  limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (fun t : ℝ => (f (u + t • y) - f u) / t)

/-- Facet datum of `f` in direction `u`: `germ f u − germ f (−u)`. -/
def germDiff {m : ℕ} (u : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) : (Fin m → ℝ) → ℝ :=
  fun y => germ f u y - germ f (-u) y

/-- Iterated facet data along a list of directions, first element first. -/
def iterGermDiff {m : ℕ} : List (Fin m → ℝ) → ((Fin m → ℝ) → ℝ) → ((Fin m → ℝ) → ℝ)
  | [], f => f
  | u :: us, f => iterGermDiff us (germDiff u f)

/-- The flag functional `Λ_{us}`: iterated facet data along `us`, evaluated at the last
direction of `us` (`0` for the empty list). -/
def flagFun {m : ℕ} (us : List (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ) : ℝ :=
  iterGermDiff us f ((us.getLast?).getD 0)

/-- A flag of `ℝ^m`: a list of `m` linearly independent directions. -/
def IsFlag {m : ℕ} (us : List (Fin m → ℝ)) : Prop :=
  us.length = m ∧ LinearIndependent ℝ (fun i : Fin us.length => us.get i)

theorem iterGermDiff_nil {m : ℕ} (f : (Fin m → ℝ) → ℝ) : iterGermDiff [] f = f := rfl

theorem iterGermDiff_cons {m : ℕ} (u : Fin m → ℝ) (us : List (Fin m → ℝ))
    (f : (Fin m → ℝ) → ℝ) : iterGermDiff (u :: us) f = iterGermDiff us (germDiff u f) := rfl

/-! ## The sweep operator -/

/-- Projection along `v` onto the hyperplane `{dot w · = 0}`: `x ↦ x − ⟨w, x⟩ v`
(meaningful when `⟨w, v⟩ = 1`). -/
def sweepProj {m : ℕ} (v w : Fin m → ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  x - (dot w x) • v

/-- The sweep operator along `v` with height functional `⟨w, ·⟩` (`⟨w, v⟩ = 1`):
`(𝒯 f)(ξ) = f ξ` if `⟨v, ξ⟩ ≥ 0`, and `f (ξ − ⟨v, ξ⟩ w)` otherwise.  For a point set `G` of
nonnegative height, `𝒯 (hS G) = hS (G ∪ sweepProj v w '' G)` (the prism down to the
hyperplane). -/
def sweep {m : ℕ} (v w : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) : (Fin m → ℝ) → ℝ :=
  fun ξ => if 0 ≤ dot v ξ then f ξ else f (ξ - (dot v ξ) • w)

/-! ## Paramid units with a finite set of labels, and the standard simplex -/

/-- The paramid unit with apex offset `γ` and a finite set `V` of edge vectors:
`relu (⟨γ, y⟩ + ∑_{v ∈ V} relu ⟨v, y⟩)`. -/
def paramidOn {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) (y : Fin m → ℝ) : ℝ :=
  relu (dot γ y + ∑ v in V, relu (dot v y))

/-- Vertex set of the cone from `0` over the parallelepiped `γ + ∑_{v ∈ V} [0, v]`. -/
def coneVertsOn {m : ℕ} (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) : Finset (Fin m → ℝ) :=
  insert 0 (V.powerset.image (fun I => γ + ∑ v in I, v))

/-- Vertex set of the standard simplex `Δ^n = conv (0, e₁, …, e_n)`. -/
def simplexVerts (n : ℕ) : Finset (Fin n → ℝ) :=
  insert 0 (Finset.univ.image (fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)))

/-! ## Reduced simplex coordinates -/

/-- Real coordinates of a lattice vector. -/
def toR {n : ℕ} (γ : Γ n) : Fin n → ℝ := fun i => (γ i : ℝ)

/-- Integer reduced coordinates embed injectively into real coordinates. -/
theorem toR_injective {n : ℕ} : Function.Injective (toR : Γ n → (Fin n → ℝ)) := by
  intro γ δ h
  funext i
  have hi := congrFun h i
  simp only [toR] at hi
  exact_mod_cast hi

end

end MaxNN.ParamidGeom
