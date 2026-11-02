import MaxCaterpillar.Fiber.Count65.Paired.RowInterpolation

/-! # Direct physical chord from a nonnegative pair to a split baseline

Only the chosen positive-output and negative-output preactivations must be
nonnegative. Every other selected gate may be nonlinear and contracts to zero.
All unselected physical neurons remain fixed throughout the path.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier Absorption

private lemma relu_mul_nonneg {a : ℝ} (ha : 0≤a) (z : ℝ) : relu (a*z)=a*relu z := by
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    simp [relu]
  · exact relu_mul_pos h z

noncomputable def splitTargetScalar {k : ℕ} (d P : Fin k → ℝ)
    (S : Finset (Fin k)) (p n : Fin k) (Q N : ℝ) : Fin k → ℝ :=
  fun i => if i=p then Q/d p else if i=n then -N/d n else if i∈S then 0 else P i

theorem split_chord_scalar {k : ℕ} (d P : Fin k → ℝ)
    (S : Finset (Fin k)) (p n : Fin k) (hpS : p∈S) (hnS : n∈S) (hpn : p≠n)
    (hdp : 0<d p) (hdn : d n<0) (hPp : 0≤P p) (hPn : 0≤P n)
    (Q N : ℝ) (hQ : 0≤Q) (hN : 0≤N)
    (hfit : (∑ i in S, d i*relu (P i))=Q-N)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (∑ i, d i*relu ((1-t)*P i+t*splitTargetScalar d P S p n Q N i))=
      ∑ i, d i*relu (P i) := by
  classical
  have ht : 0≤1-t := sub_nonneg.mpr ht1
  have hdelta : ∀ i, d i*relu ((1-t)*P i+t*splitTargetScalar d P S p n Q N i)=
      d i*relu (P i)-(if i∈S then t*(d i*relu (P i)) else 0)+
        (if i=p then t*Q else 0)-(if i=n then t*N else 0) := by
    intro i
    by_cases hip : i=p
    · subst i
      have hnew : 0≤(1-t)*P p+t*(Q/d p) :=
        add_nonneg (mul_nonneg ht hPp) (mul_nonneg ht0 (div_nonneg hQ hdp.le))
      simp only [splitTargetScalar,if_pos rfl,if_pos hpS,if_neg hpn,sub_zero,if_true,if_false]
      rw [relu_of_nonneg hnew,relu_of_nonneg hPp]
      field_simp [ne_of_gt hdp]
      ring
    · by_cases hin : i=n
      · subst i
        have hnew : 0≤(1-t)*P n+t*(-N/d n) :=
          add_nonneg (mul_nonneg ht hPn)
            (mul_nonneg ht0 (div_nonneg_of_nonpos (neg_nonpos.mpr hN) hdn.le))
        simp only [splitTargetScalar,if_neg (Ne.symm hpn),if_pos rfl,if_pos hnS,add_zero,if_true,if_false]
        rw [relu_of_nonneg hnew,relu_of_nonneg hPn]
        field_simp [ne_of_lt hdn]
        ring
      · by_cases hi : i∈S
        · simp only [splitTargetScalar,if_neg hip,if_neg hin,if_pos hi,mul_zero,add_zero,
            sub_zero]
          rw [relu_mul_nonneg ht]
          ring
        · simp only [splitTargetScalar,if_neg hip,if_neg hin,if_neg hi,mul_zero,
            sub_zero,add_zero]
          congr 2
          ring
  simp_rw [hdelta]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hsum : (∑ i, if i∈S then t*(d i*relu (P i)) else 0)=t*(Q-N) := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun i => i∈S)=S := by ext i; simp
    rw [hf,← Finset.mul_sum,hfit]
  rw [hsum]
  ring

noncomputable def splitTargetRows {N m k : ℕ} (net : Network N m k)
    (Qrow Nrow : Fin m → ℝ) (S : Finset (Fin k)) (p n : Fin k) : Fin k → Fin m → ℝ :=
  fun i j => if i=p then Qrow j/net.w₃ p else if i=n then -Nrow j/net.w₃ n
    else if i∈S then 0 else net.W₂ i j

noncomputable def splitTargetBiases {N m k : ℕ} (net : Network N m k)
    (Qbias Nbias : ℝ) (S : Finset (Fin k)) (p n : Fin k) : Fin k → ℝ :=
  fun i => if i=p then Qbias/net.w₃ p else if i=n then -Nbias/net.w₃ n
    else if i∈S then 0 else net.b₂ i

private lemma preact_div {N m : ℕ} (A : Fin m → Point N)
    (β row : Fin m → ℝ) (bias c : ℝ) (x : Point N) :
    preact A β (fun j => row j/c) (bias/c) x=preact A β row bias x/c := by
  have hh := preact_smul A β row bias (c⁻¹) x
  simpa only [div_eq_mul_inv,mul_comm] using hh

lemma splitTarget_preact {N m k : ℕ} (net : Network N m k)
    (Qrow Nrow : Fin m → ℝ) (Qbias Nbias : ℝ)
    (S : Finset (Fin k)) (p n i : Fin k) (x : Point N) :
    preact net.W₁ net.b₁ (splitTargetRows net Qrow Nrow S p n i)
        (splitTargetBiases net Qbias Nbias S p n i) x=
      splitTargetScalar net.w₃ (fun j => preact net.W₁ net.b₁ (net.W₂ j) (net.b₂ j) x)
        S p n (preact net.W₁ net.b₁ Qrow Qbias x) (preact net.W₁ net.b₁ Nrow Nbias x) i := by
  unfold splitTargetRows splitTargetBiases splitTargetScalar
  by_cases hip : i=p
  · simp only [splitTargetRows,splitTargetBiases,splitTargetScalar,if_pos hip]
    exact preact_div _ _ _ _ _ _
  · by_cases hin : i=n
    · simp only [splitTargetRows,splitTargetBiases,splitTargetScalar,if_neg hip,if_pos hin]
      rw [preact_div,preact_neg]
    · by_cases hi : i∈S
      · simp [splitTargetRows,splitTargetBiases,splitTargetScalar,hip,hin,hi,preact]
      · simp [splitTargetRows,splitTargetBiases,splitTargetScalar,hip,hin,hi]

noncomputable def splitChord {N m k : ℕ} (net : Network N m k)
    (Qrow Nrow : Fin m → ℝ) (Qbias Nbias : ℝ)
    (S : Finset (Fin k)) (p n : Fin k) (t : ℝ) : Network N m k :=
  interpolateSecondRows net (splitTargetRows net Qrow Nrow S p n)
    (splitTargetBiases net Qbias Nbias S p n) t

theorem splitChord_eval {N m k : ℕ} (net : Network N m k)
    (Qrow Nrow : Fin m → ℝ) (Qbias Nbias : ℝ)
    (S : Finset (Fin k)) (p n : Fin k) (hpS : p∈S) (hnS : n∈S) (hpn : p≠n)
    (hdp : 0<net.w₃ p) (hdn : net.w₃ n<0)
    (hPp : ∀ x, 0≤preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x)
    (hPn : ∀ x, 0≤preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x)
    (hQ : ∀ x, 0≤preact net.W₁ net.b₁ Qrow Qbias x)
    (hN : ∀ x, 0≤preact net.W₁ net.b₁ Nrow Nbias x)
    (hfit : ∀ x, (∑ i in S, net.w₃ i*relu
      (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x))=
        preact net.W₁ net.b₁ Qrow Qbias x-preact net.W₁ net.b₁ Nrow Nbias x)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) (x : Point N) :
    (splitChord net Qrow Nrow Qbias Nbias S p n t).eval x=net.eval x := by
  change (∑ i, net.w₃ i*relu (preact net.W₁ net.b₁
      (((1-t) • net.W₂+t • splitTargetRows net Qrow Nrow S p n) i)
      (((1-t) • net.b₂+t • splitTargetBiases net Qbias Nbias S p n) i) x))+net.b₃ = _
  simp_rw [interpolateSecondRows_preact,splitTarget_preact]
  congr 1
  exact split_chord_scalar net.w₃ _ S p n hpS hnS hpn hdp hdn (hPp x) (hPn x)
    _ _ (hQ x) (hN x) (hfit x) t ht0 ht1

/-- Exact physical split-baseline attachment, with every unselected gate fixed. -/
theorem splitChord_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : Network N m k) (Qrow Nrow : Fin m → ℝ) (Qbias Nbias : ℝ)
    (S : Finset (Fin k)) (p n : Fin k) (hpS : p∈S) (hnS : n∈S) (hpn : p≠n)
    (hdp : 0<net.w₃ p) (hdn : net.w₃ n<0)
    (hPp : ∀ x, 0≤preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x)
    (hPn : ∀ x, 0≤preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x)
    (hQ : ∀ x, 0≤preact net.W₁ net.b₁ Qrow Qbias x)
    (hN : ∀ x, 0≤preact net.W₁ net.b₁ Nrow Nbias x)
    (hfit : ∀ x, (∑ i in S, net.w₃ i*relu
      (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x))=
        preact net.W₁ net.b₁ Qrow Qbias x-preact net.W₁ net.b₁ Nrow Nbias x)
    (hnet : ∀ x, net.eval x=Maximum N x) :
    JoinedIn (ExactSet N m k) net
      (withSecondRows net (splitTargetRows net Qrow Nrow S p n)
        (splitTargetBiases net Qbias Nbias S p n)) := by
  apply JoinedIn.ofLine (continuous_interpolateSecondRows net
    (splitTargetRows net Qrow Nrow S p n) (splitTargetBiases net Qbias Nbias S p n)).continuousOn
  · exact interpolateSecondRows_zero _ _ _
  · exact interpolateSecondRows_one _ _ _
  · rintro _ ⟨t,ht,rfl⟩ x
    change (splitChord net Qrow Nrow Qbias Nbias S p n t).eval x=Maximum N x
    exact (splitChord_eval net Qrow Nrow Qbias Nbias S p n hpS hnS hpn hdp hdn
      hPp hPn hQ hN hfit t ht.1 ht.2 x).trans (hnet x)

end MaxCaterpillar.Fiber.Count65.Paired
