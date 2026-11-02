import research.sN.exponential_push_20261102.ridge_annihilator.RankBridge
import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
import MaxCaterpillar.Frontier.SecondWidthN

/-! An original second-hidden-layer neuron must observe at least `N−1`
independent input directions. Biases and all affine skips are unrestricted. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.Ridge
open BigOperators Frontier Frontier.RandomRestriction.AffineSkipExtension

variable {N h₁ h₂ : ℕ} [NeZero N]

/-- The actual input-skip covector together with the feeding first covectors.
Multiplication by `W k j` removes precisely the nonfeeding rows and otherwise
only rescales them, so the range rank is the rank of their joint observation. -/
def secondObservation (net : AffineSkipNetwork N h₁ h₂) (k : Fin h₂) :
    Point N →ₗ[ℝ] ℝ × (Fin h₁ → ℝ) :=
  (linMap (net.U k)).prod (LinearMap.pi fun j => net.W k j • linMap (net.A j))

lemma secondObservation_apply (net : AffineSkipNetwork N h₁ h₂) (k : Fin h₂)
    (x : Point N) :
    secondObservation net k x = (lin (net.U k) x, fun j => net.W k j * lin (net.A j) x) := rfl

lemma first_period_of_lin_zero (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁)
    (v : Point N) (hv : lin (net.A j) v = 0) (x : Point N) :
    first net j (x + v) = first net j x := by
  change relu (lin (net.A j) (x+v)+net.b j) = relu (lin (net.A j) x+net.b j)
  rw [lin_add_right,hv,add_zero]

lemma inner_period_of_observation_zero (net : AffineSkipNetwork N h₁ h₂)
    (k : Fin h₂) (v : Point N) (hv : secondObservation net k v = 0)
    (x : Point N) : inner net k (x+v) = inner net k x := by
  have hU : lin (net.U k) v = 0 := congrArg Prod.fst hv
  have hW : ∀ j, net.W k j * lin (net.A j) v = 0 := fun j =>
    congrFun (congrArg Prod.snd hv) j
  change (∑ j,net.W k j*first net j (x+v))+lin (net.U k) (x+v)+net.θ k =
    (∑ j,net.W k j*first net j x)+lin (net.U k) x+net.θ k
  rw [lin_add_right,hU,add_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : net.W k j = 0
  · simp only [hj,zero_mul]
  · rw [first_period_of_lin_zero net j v ((mul_eq_zero.mp (hW j)).resolve_left hj) x]

/-- No normalization or row-support hypothesis is imposed. The witness is
one of the original second-hidden-layer indices, with its original weights. -/
theorem exists_active_original_second_highrank (hN : 3 ≤ N)
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x, eval net x = Maximum N x) :
    ∃ k : Fin h₂, net.d k ≠ 0 ∧
      N - 1 ≤ FiniteDimensional.finrank ℝ (LinearMap.range (secondObservation net k)) := by
  classical
  by_contra! hsmall
  have hN2 : 2 ≤ N := (by norm_num : 2 ≤ 3).trans hN
  have hscalar : FiniteDimensional.finrank ℝ ℝ ≤ N - 2 := by
    rw [FiniteDimensional.finrank_self]
    exact (Nat.le_sub_iff_add_le hN2).mpr hN
  let f : Fin h₁ ⊕ Fin h₂ → Point N → ℝ :=
    Sum.elim (fun j x => net.B j * first net j x)
      (fun k x => net.d k * relu (inner net k x))
  have hf : ∀ s, ∃ v : Point N, (∃ i j, v i ≠ v j) ∧
      ∀ x, f s (x+v) = f s x := by
    intro s
    rcases s with j | k
    · obtain ⟨v,hv,hnd⟩ := exists_nondiagonal_ker_of_finrank hN2 (linMap (net.A j)) hscalar
      refine ⟨v,hnd,?_⟩
      intro x
      change net.B j * first net j (x+v) = net.B j * first net j x
      rw [first_period_of_lin_zero net j v hv x]
    · by_cases hd : net.d k = 0
      · obtain ⟨v,_,hnd⟩ := exists_nondiagonal_ker_of_finrank hN2
          (0 : Point N →ₗ[ℝ] ℝ) hscalar
        refine ⟨v,hnd,?_⟩
        intro x
        change net.d k * relu (inner net k (x+v)) = net.d k * relu (inner net k x)
        simp only [hd,zero_mul]
      have hk : FiniteDimensional.finrank ℝ
          (LinearMap.range (secondObservation net k)) ≤ N-2 := by
        have hh := Nat.le_pred_of_lt (hsmall k hd)
        simpa only [Nat.pred_eq_sub_one,Nat.sub_sub] using hh
      obtain ⟨v,hv,hnd⟩ := exists_nondiagonal_ker_of_finrank hN2
        (secondObservation net k).rangeRestrict hk
      have hv' : secondObservation net k v = 0 := congrArg Subtype.val hv
      refine ⟨v,hnd,?_⟩
      intro x
      change net.d k * relu (inner net k (x+v)) = net.d k * relu (inner net k x)
      rw [inner_period_of_observation_zero net k v hv' x]
  apply maximum_ne_affine_sum_of_exists_periods hN2 f hf (linMap net.L).toAddMonoidHom net.β
  intro x
  rw [← hmax x]
  simp only [f,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,eval,outputSkip]
  change (∑ k,net.d k*relu (inner net k x))+
      ((∑ j,net.B j*first net j x)+lin net.L x+net.β) =
    lin net.L x+net.β+((∑ j,net.B j*first net j x)+(∑ k,net.d k*relu (inner net k x)))
  ring

theorem exists_original_second_highrank (hN : 3 ≤ N)
    (net : AffineSkipNetwork N h₁ h₂)
    (hmax : ∀ x, eval net x = Maximum N x) :
    ∃ k : Fin h₂,
      N - 1 ≤ FiniteDimensional.finrank ℝ (LinearMap.range (secondObservation net k)) := by
  obtain ⟨k,_,hk⟩ := exists_active_original_second_highrank hN net hmax
  exact ⟨k,hk⟩

#check @exists_original_second_highrank
#check @exists_active_original_second_highrank
#print axioms inner_period_of_observation_zero
#print axioms exists_original_second_highrank
#print axioms exists_active_original_second_highrank
end MaxCaterpillar.ExponentialPush.Ridge
