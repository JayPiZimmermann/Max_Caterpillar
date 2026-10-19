import MaxNN.Constructions.Paramid.Unit
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.BigOperators.Basic

/-!
# `dot` is a symmetric bilinear form (helper for `PolyhedralGeometry/SupportCut.lean`)

`MaxNN.dot v y = ∑ᵢ vᵢ yᵢ` (`Constructions/Paramid/Unit.lean`).  This file records that it is
symmetric and bilinear, packages `p ↦ ⟨a, p⟩` as a linear functional `dotL a`, and proves
`⟨a, a⟩ = 0 → a = 0`.
-/

namespace MaxNN

namespace SupportCut

open BigOperators

variable {N : ℕ}

theorem dot_comm (v w : Fin N → ℝ) : dot v w = dot w v := by
  show ∑ i, v i * w i = ∑ i, w i * v i
  exact Finset.sum_congr rfl fun i _ => mul_comm (v i) (w i)

theorem dot_add_left (u v y : Fin N → ℝ) : dot (u + v) y = dot u y + dot v y := by
  show ∑ i, (u + v) i * y i = ∑ i, u i * y i + ∑ i, v i * y i
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_mul (u i) (v i) (y i)

theorem dot_smul_left (r : ℝ) (u y : Fin N → ℝ) : dot (r • u) y = r * dot u y := by
  show ∑ i, (r • u) i * y i = r * ∑ i, u i * y i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_assoc r (u i) (y i)

theorem dot_sub_left (u v y : Fin N → ℝ) : dot (u - v) y = dot u y - dot v y := by
  show ∑ i, (u - v) i * y i = ∑ i, u i * y i - ∑ i, v i * y i
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => sub_mul (u i) (v i) (y i)

theorem dot_add_right (a u v : Fin N → ℝ) : dot a (u + v) = dot a u + dot a v := by
  rw [dot_comm a, dot_add_left, dot_comm u, dot_comm v]

theorem dot_smul_right (r : ℝ) (a u : Fin N → ℝ) : dot a (r • u) = r * dot a u := by
  rw [dot_comm a, dot_smul_left, dot_comm u]

theorem dot_sub_right (a u v : Fin N → ℝ) : dot a (u - v) = dot a u - dot a v := by
  rw [dot_comm a, dot_sub_left, dot_comm u, dot_comm v]

/-- `p ↦ ⟨a, p⟩` as an `ℝ`-linear functional on `ℝ^N`. -/
noncomputable def dotL (a : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun p := dot a p
  map_add' u v := dot_add_right a u v
  map_smul' r u := by
    show dot a (r • u) = (RingHom.id ℝ) r • dot a u
    rw [RingHom.id_apply, smul_eq_mul]
    exact dot_smul_right r a u

theorem dotL_apply (a p : Fin N → ℝ) : dotL a p = dot a p := rfl

/-- `⟨a, ∑ᵢ wᵢ zᵢ⟩ = ∑ᵢ wᵢ ⟨a, zᵢ⟩`. -/
theorem dot_sum_smul_right {ι : Type*} (a : Fin N → ℝ) (T : Finset ι) (w : ι → ℝ)
    (z : ι → Fin N → ℝ) : dot a (∑ i in T, w i • z i) = ∑ i in T, w i * dot a (z i) := by
  rw [← dotL_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.map_smul, smul_eq_mul, dotL_apply]

/-- `⟨a, a⟩ = 0` forces `a = 0`. -/
theorem eq_zero_of_dot_self_eq_zero {a : Fin N → ℝ} (h : dot a a = 0) : a = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (a i)).mp h
  funext i
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

end SupportCut

end MaxNN
