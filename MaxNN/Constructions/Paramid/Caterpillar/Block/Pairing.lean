import MaxNN.Constructions.Paramid.Geom.Germ

/-! # Finite pairing modulo a linear subspace

Pairing is allowed to fix terms already in the subspace. This avoids adding
an artificial fixed-point-free hypothesis when discarding lower-order terms.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

theorem sum_mem_of_equiv_pair (U : Submodule ℝ V) (f : ι → V) (e : ι ≃ ι)
    (hpair : ∀ i, f i + f (e i) ∈ U) : (∑ i, f i) ∈ U := by
  have he : (∑ i, f (e i)) = ∑ i, f i :=
    Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)
  have hs := Submodule.sum_mem U (fun i (_ : i ∈ Finset.univ) => hpair i)
  rw [Finset.sum_add_distrib, he] at hs
  have ht := Submodule.smul_mem U (1 / 2 : ℝ) hs
  have hid : (1 / 2 : ℝ) • ((∑ i, f i) + ∑ i, f i) = ∑ i, f i := by
    rw [smul_add, ← add_smul]
    norm_num
  rwa [hid] at ht

theorem sum_mem_of_involutive_pair (U : Submodule ℝ V) (f : ι → V) (e : ι → ι)
    (he : Function.Involutive e) (hpair : ∀ i, f i + f (e i) ∈ U) :
    (∑ i, f i) ∈ U :=
  sum_mem_of_equiv_pair U f ⟨e, e, he, he⟩ hpair

/-- An entire finite orbit may replace a pair. Every permutation occurs the
same number of times, so a nonempty orbit average preserves subspace membership. -/
theorem sum_mem_of_equiv_average {J : Type*} [Fintype J] [Nonempty J]
    (U : Submodule ℝ V) (f : ι → V) (e : J → ι ≃ ι)
    (haverage : ∀ i, (∑ j, f (e j i)) ∈ U) : (∑ i, f i) ∈ U := by
  have hs := Submodule.sum_mem U (fun i (_ : i ∈ Finset.univ) => haverage i)
  rw [Finset.sum_comm] at hs
  have he : ∀ j, (∑ i, f (e j i)) = ∑ i, f i := fun j =>
    Fintype.sum_equiv (e j) (fun i => f (e j i)) f (fun _ => rfl)
  simp_rw [he] at hs
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_smul_cast ℝ] at hs
  have hcard : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ht := Submodule.smul_mem U ((Fintype.card J : ℝ)⁻¹) hs
  rwa [smul_smul, inv_mul_cancel hcard, one_smul] at ht

end MaxNN.Caterpillar
