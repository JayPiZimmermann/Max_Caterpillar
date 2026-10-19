import MaxNN.Constructions.Paramid.Geom.Defs

/-!
# Face matrices of the standard simplex

Shared definitions for `Geom/Induction.lean` and its helpers.  The face relabelling
`ι_j = Fin.succAbove j` of the chain complex acts on lattice vectors by
`latticeMap j.succAbove : Γ n → Γ (n + 1)` (`Paramid/Chain/Root.lean`).

* `faceMat j` — its real matrix: column `k` is `vtx (j.succAbove k.succ) − vtx (j.succAbove 0)`.
* `faceFrame j u` — the square matrix with columns `u, (faceMat j)_{·0}, …, (faceMat j)_{·(n−1)}`.
* `faceCoef j u` — the orientation coefficient of the `j`-th face in the facet datum in direction
  `u`: `sign det (faceFrame j u)` if `u` is orthogonal to the face hyperplane, else `0`.
* `nu j` — the outer normal of the facet of `Δ^{n+1} = conv (0, e₀, …, e_n)` opposite `vtx j`:
  `nu 0 = (1, …, 1)`, `nu (i + 1) = − e_i`.
-/

namespace MaxNN.ParamidGeom

open BigOperators Matrix MaxNN.ParamidChain

noncomputable section

/-- Real matrix of the face relabelling `latticeMap j.succAbove : Γ n → Γ (n + 1)`. -/
def faceMat {n : ℕ} (j : Fin (n + 2)) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  Matrix.of fun i k => ((vtx (j.succAbove k.succ) - vtx (j.succAbove 0) : Γ (n + 1)) i : ℝ)

/-- The square matrix with columns `u, (faceMat j)_{·0}, …, (faceMat j)_{·(n−1)}`. -/
def faceFrame {n : ℕ} (j : Fin (n + 2)) (u : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i => (Fin.cons (u i) (faceMat j i) : Fin (n + 1) → ℝ)

/-- Orientation coefficient of the `j`-th face in direction `u`: `sign det [u | faceMat j]` if
`(faceMat j)ᵀ u = 0`, and `0` otherwise. -/
def faceCoef {n : ℕ} (j : Fin (n + 2)) (u : Fin (n + 1) → ℝ) : ℝ :=
  if (faceMat j)ᵀ.mulVec u = 0 then ((SignType.sign (faceFrame j u).det : ℤ) : ℝ) else 0

/-- Outer normal of the facet of `Δ^{n+1}` opposite `vtx j`. -/
def nu {n : ℕ} (j : Fin (n + 2)) : Fin (n + 1) → ℝ :=
  Fin.cases (fun _ => 1) (fun i => -(Pi.single i 1 : Fin (n + 1) → ℝ)) j

theorem faceMat_apply {n : ℕ} (j : Fin (n + 2)) (i : Fin (n + 1)) (k : Fin n) :
    faceMat j i k = ((vtx (j.succAbove k.succ) - vtx (j.succAbove 0) : Γ (n + 1)) i : ℝ) :=
  rfl

theorem faceFrame_apply {n : ℕ} (j : Fin (n + 2)) (u : Fin (n + 1) → ℝ) (i k : Fin (n + 1)) :
    faceFrame j u i k = (Fin.cons (u i) (faceMat j i) : Fin (n + 1) → ℝ) k :=
  rfl

theorem nu_zero {n : ℕ} : nu (0 : Fin (n + 2)) = fun _ => 1 :=
  rfl

theorem nu_succ {n : ℕ} (i : Fin (n + 1)) : nu i.succ = -(Pi.single i 1 : Fin (n + 1) → ℝ) :=
  rfl

/-- The real matrix realizes the lattice map. -/
theorem toR_latticeMap {n : ℕ} (j : Fin (n + 2)) (γ : Γ n) :
    toR (latticeMap j.succAbove γ) = (faceMat j).mulVec (toR γ) := by
  funext i
  show ((∑ k : Fin n, γ k • (vtx (j.succAbove k.succ) - vtx (j.succAbove 0))) i : ℝ) =
    ∑ k : Fin n, faceMat j i k * (γ k : ℝ)
  rw [Finset.sum_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [faceMat_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_comm]

end

end MaxNN.ParamidGeom
