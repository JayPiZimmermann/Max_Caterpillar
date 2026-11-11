import MaxCaterpillar.Fiber.Count65.Star.CarrierForcing
import MaxCaterpillar.Fiber.Mixed65.ThreeGateOrdering

/-! # Reindexing every exact three-gate star residual by its forced roles

The gate equivalence preserves the original real weights. Its roles and signs
are conclusions of the all-input identity, rather than assumptions defining a
restricted class of residual representations.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Fiber.Mixed65

lemma representsStar_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : CoefficientSystem ι) (e : κ ≃ ι) (r : ℝ) (H : RepresentsStar d r) :
    RepresentsStar (d.reindex e) r := by
  intro q b c
  have hs := Fintype.sum_equiv e
    (fun j => (d.reindex e).out j * MaxCaterpillar.relu (starGate (d.reindex e) r j q b c))
    (fun i => d.out i * MaxCaterpillar.relu (starGate d r i q b c)) (fun _ => rfl)
  change max (max 0 (q + b)) (max b (MaxCaterpillar.relu c)) = starBase d r q b c + _
  rw [hs]
  exact H q b c

private theorem three_index_equiv {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 3) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ e : Fin 3 ≃ ι, e 0 = i ∧ e 1 = j ∧ e 2 = k := by
  let f : Fin 3 → ι := ![i,j,k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f,hij,hik,hjk,Ne.symm hij,Ne.symm hik,Ne.symm hjk]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp [hcard]⟩
  exact ⟨Equiv.ofBijective f hbij,rfl,rfl,rfl⟩

/-- All three actual gates have nonzero independent-coordinate coefficient and
can be ordered as the two forced positive carriers followed by the negative gate. -/
theorem exists_ordered_three {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) (hcard : Fintype.card ι = 3) :
    ∃ e : Fin 3 ≃ ι,
      RepresentsStar (d.reindex e) r ∧
      0 < (d.reindex e).out 0 ∧ 0 < (d.reindex e).out 1 ∧
      (d.reindex e).out 2 < 0 ∧
      (∀ j, (d.reindex e).W j ≠ 0) ∧
      (d.reindex e).U 0 + (d.reindex e).W 0 + (d.reindex e).T 0 = 0 ∧
      (d.reindex e).W 0 + r * (d.reindex e).T 0 = 0 ∧
      (d.reindex e).T 1 = 0 ∧
      (d.reindex e).V 1 + (d.reindex e).W 1 = 0 := by
  obtain ⟨i, hi, hiW, hiU, hiT⟩ := exists_left_carrier d r hr hr1 H
  obtain ⟨j, hj, hjW, hjT, hjV⟩ := exists_right_carrier d r hr H
  obtain ⟨k, hk, hkW⟩ := exists_negative_active_gate d r hr hr1 H
  have hij : i ≠ j := by
    intro he
    subst j
    rw [hjT,mul_zero,add_zero] at hiT
    exact hiW hiT
  have hik : i ≠ k := by intro he; subst k; linarith only [hi,hk]
  have hjk : j ≠ k := by intro he; subst k; linarith only [hj,hk]
  obtain ⟨e,h0,h1,h2⟩ := three_index_equiv hcard i j k hij hik hjk
  refine ⟨e,representsStar_reindex d e r H,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h0] using hi
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h1] using hj
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h2] using hk
  · intro a
    fin_cases a
    · change d.W (e (0 : Fin 3)) ≠ 0
      rw [h0]
      exact hiW
    · change d.W (e (1 : Fin 3)) ≠ 0
      rw [h1]
      exact hjW
    · change d.W (e (2 : Fin 3)) ≠ 0
      rw [h2]
      exact hkW
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h0] using hiU
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h0] using hiT
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h1] using hjT
  · simpa only [ResidualSystem.reindex,Function.comp_apply,h1] using hjV

end MaxCaterpillar.Fiber.Count65.Star
