import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.ClusterPath
import MaxCaterpillar.Fiber.Count65.Paired.RowInterpolation

/-! # A signed pair absorbs an entire finite physical completion by one chord

Two existing readout slots have coefficients `1,-1` and functionally opposite
preactivations. Interpolate them to a chosen affine target and its negative,
and contract every other selected incoming row and bias. The selected group's
function is unchanged; all spectators retain their physical parameters.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators Absorption

noncomputable def signedChordRows {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n : Fin k) (L : Fin m → ℝ) : Fin k → Fin m → ℝ :=
  fun i => if i=p then L else if i=n then -L else if i ∈ s then 0 else net.W₂ i

noncomputable def signedChordBiases {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n : Fin k) (η : ℝ) : Fin k → ℝ :=
  fun i => if i=p then η else if i=n then -η else if i ∈ s then 0 else net.b₂ i

noncomputable def signedChordNet {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n : Fin k) (L : Fin m → ℝ) (η t : ℝ) : Network N m k :=
  interpolateSecondRows net (signedChordRows net s p n L) (signedChordBiases net s p n η) t

private theorem sum_pair_rest {k : ℕ} (s : Finset (Fin k)) (p n : Fin k)
    (hp : p ∈ s) (hn : n ∈ s) (hpn : p ≠ n) (f : Fin k → ℝ) :
    (∑ i in s, f i) = f p+f n+∑ i in (s.erase p).erase n, f i := by
  have hn' : n ∈ s.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpn,hn⟩
  rw [← Finset.add_sum_erase s f hp,← Finset.add_sum_erase (s.erase p) f hn']
  ring

private theorem signedChord_target_preact {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n i : Fin k) (L : Fin m → ℝ) (η : ℝ) (x : Point N) :
    preact net.W₁ net.b₁ (signedChordRows net s p n L i)
      (signedChordBiases net s p n η i) x =
      if i=p then preact net.W₁ net.b₁ L η x
      else if i=n then -preact net.W₁ net.b₁ L η x
      else if i ∈ s then 0 else preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x := by
  by_cases hip : i=p
  · simp only [signedChordRows,signedChordBiases,if_pos hip]
  · by_cases hin : i=n
    · simp only [signedChordRows,signedChordBiases,if_neg hip,if_pos hin]
      exact preact_neg net.W₁ net.b₁ L η x
    · by_cases hi : i ∈ s
      · simp only [signedChordRows,signedChordBiases,if_neg hip,if_neg hin,if_pos hi]
        simp [preact]
      · simp only [signedChordRows,signedChordBiases,if_neg hip,if_neg hin,if_neg hi]

/-- The source pair need only be opposite as functions of natural first-layer
features. The other selected slots have arbitrary signs and arbitrary knots. -/
theorem signedChord_eval {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n : Fin k) (hp : p ∈ s) (hn : n ∈ s) (hpn : p ≠ n)
    (hdp : net.w₃ p = 1) (hdn : net.w₃ n = -1)
    (hneg : ∀ x, preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x =
      -preact net.W₁ net.b₁ (net.W₂ p) (net.b₂ p) x)
    (L : Fin m → ℝ) (η : ℝ)
    (hfit : ∀ x, (∑ i in s, net.w₃ i*relu
      (preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x)) = preact net.W₁ net.b₁ L η x)
    (t : ℝ) (ht : t ≤ 1) (x : Point N) :
    (signedChordNet net s p n L η t).eval x = net.eval x := by
  classical
  let Z := fun i => preact net.W₁ net.b₁ (net.W₂ i) (net.b₂ i) x
  let Z' := fun i => preact net.W₁ net.b₁
    (((1-t) • net.W₂+t • signedChordRows net s p n L) i)
    (((1-t) • net.b₂+t • signedChordBiases net s p n η) i) x
  let T := preact net.W₁ net.b₁ L η x
  have hz (i : Fin k) : Z' i = (1-t)*Z i+t*
      (if i=p then T else if i=n then -T else if i ∈ s then 0 else Z i) := by
    have h := interpolateSecondRows_preact net (signedChordRows net s p n L)
      (signedChordBiases net s p n η) t i x
    rw [signedChord_target_preact] at h
    exact h
  have hpz : Z' p = (1-t)*Z p+t*T := by
    rw [hz p,if_pos rfl]
  have hnz : Z' n = -Z' p := by
    rw [hz n,if_neg (Ne.symm hpn),if_pos rfl,hpz]
    change (1-t)*preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x+t*(-T) = _
    rw [hneg x]
    ring
  have hdiff (u : ℝ) : relu u-relu (-u) = u := by
    simpa only [relu,max_comm] using max_zero_sub_max_neg_zero_eq_self u
  have hpair : net.w₃ p*relu (Z p)+net.w₃ n*relu (Z n) = Z p := by
    rw [hdp,hdn,one_mul,neg_one_mul]
    change relu (Z p)-relu (preact net.W₁ net.b₁ (net.W₂ n) (net.b₂ n) x) = Z p
    rw [hneg x]
    exact hdiff (Z p)
  have hpair' : net.w₃ p*relu (Z' p)+net.w₃ n*relu (Z' n) = Z' p := by
    rw [hdp,hdn,one_mul,neg_one_mul,hnz]
    exact hdiff (Z' p)
  have hrest : (∑ i in (s.erase p).erase n, net.w₃ i*relu (Z' i)) =
      (1-t)*(∑ i in (s.erase p).erase n, net.w₃ i*relu (Z i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rcases Finset.mem_erase.mp hi with ⟨hin,hi⟩
    rcases Finset.mem_erase.mp hi with ⟨hip,hi⟩
    rw [hz i,if_neg hip,if_neg hin,if_pos hi,mul_zero,add_zero]
    have hscale : relu ((1-t)*Z i) = (1-t)*relu (Z i) := by
      change max 0 ((1-t)*Z i) = (1-t)*max 0 (Z i)
      rw [mul_max_of_nonneg _ _ (sub_nonneg.mpr ht),mul_zero]
    rw [hscale]
    ring
  have hsource : Z p+(∑ i in (s.erase p).erase n, net.w₃ i*relu (Z i)) = T := by
    have h := hfit x
    rw [sum_pair_rest s p n hp hn hpn] at h
    change net.w₃ p*relu (Z p)+net.w₃ n*relu (Z n)+_ = T at h
    rw [hpair] at h
    exact h
  have hlocal : (∑ i in s, net.w₃ i*relu (Z' i)) =
      ∑ i in s, net.w₃ i*relu (Z i) := by
    rw [sum_pair_rest s p n hp hn hpn,sum_pair_rest s p n hp hn hpn,
      hpair',hpair,hrest,hpz]
    calc
      _ = (1-t)*(Z p+(∑ i in (s.erase p).erase n, net.w₃ i*relu (Z i)))+t*T := by ring
      _ = Z p+(∑ i in (s.erase p).erase n, net.w₃ i*relu (Z i)) := by
        rw [hsource]
        ring
  have houtside : ∀ i ∉ s, Z' i = Z i := by
    intro i hi
    have hip : i ≠ p := by rintro rfl; exact hi hp
    have hin : i ≠ n := by rintro rfl; exact hi hn
    rw [hz i,if_neg hip,if_neg hin,if_neg hi]
    ring
  have hfilter : Finset.univ.filter (fun i => i ∈ s) = s := by ext i; simp
  have hsplit (f : Fin k → ℝ) : (∑ i, f i) =
      (∑ i in s, f i)+∑ i in Finset.univ.filter (fun i => i ∉ s), f i := by
    have h := (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (fun i => i ∈ s) f).symm
    rw [hfilter] at h
    exact h
  change (∑ i, net.w₃ i*relu (Z' i))+net.b₃ = (∑ i, net.w₃ i*relu (Z i))+net.b₃
  congr 1
  rw [hsplit,hsplit,hlocal]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [houtside i (Finset.mem_filter.mp hi).2]

theorem signedChord_joinedIn_exact {N m k : ℕ} [NeZero N]
    (net : ExactFiber N m k) (s : Finset (Fin k)) (p n : Fin k)
    (hp : p ∈ s) (hn : n ∈ s) (hpn : p ≠ n)
    (hdp : net.val.w₃ p = 1) (hdn : net.val.w₃ n = -1)
    (hneg : ∀ x, preact net.val.W₁ net.val.b₁ (net.val.W₂ n) (net.val.b₂ n) x =
      -preact net.val.W₁ net.val.b₁ (net.val.W₂ p) (net.val.b₂ p) x)
    (L : Fin m → ℝ) (η : ℝ)
    (hfit : ∀ x, (∑ i in s, net.val.w₃ i*relu
      (preact net.val.W₁ net.val.b₁ (net.val.W₂ i) (net.val.b₂ i) x)) =
        preact net.val.W₁ net.val.b₁ L η x) :
    JoinedIn (ExactSet N m k) net.val
      (withSecondRows net.val (signedChordRows net.val s p n L)
        (signedChordBiases net.val s p n η)) := by
  apply JoinedIn.ofLine (continuous_interpolateSecondRows net.val
    (signedChordRows net.val s p n L) (signedChordBiases net.val s p n η)).continuousOn
    (interpolateSecondRows_zero _ _ _) (interpolateSecondRows_one _ _ _)
  rintro _ ⟨t,ht,rfl⟩ x
  change (signedChordNet net.val s p n L η t).eval x = Maximum N x
  rw [signedChord_eval net.val s p n hp hn hpn hdp hdn hneg L η hfit t ht.2 x]
  exact net.property x

theorem signedChord_endpoint_unused {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n i : Fin k) (L : Fin m → ℝ) (η : ℝ)
    (hi : i ∈ s) (hip : i ≠ p) (hin : i ≠ n) :
    (withSecondRows net (signedChordRows net s p n L) (signedChordBiases net s p n η)).W₂ i = 0 ∧
    (withSecondRows net (signedChordRows net s p n L) (signedChordBiases net s p n η)).b₂ i = 0 := by
  simp [withSecondRows,signedChordRows,signedChordBiases,hip,hin,hi]

theorem signedChord_endpoint_pair {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n : Fin k) (L : Fin m → ℝ) (η : ℝ) (hpn : p ≠ n) :
    let target := withSecondRows net (signedChordRows net s p n L)
      (signedChordBiases net s p n η)
    target.W₂ p = L ∧ target.b₂ p = η ∧ target.W₂ n = -L ∧ target.b₂ n = -η := by
  simp [withSecondRows,signedChordRows,signedChordBiases,Ne.symm hpn]

/-- The indexed chord retains every incoming parameter of each spectator
throughout the path; the first and output layers are fixed by construction. -/
theorem signedChord_spectator {N m k : ℕ} (net : Network N m k)
    (s : Finset (Fin k)) (p n i : Fin k) (hp : p ∈ s) (hn : n ∈ s)
    (hi : i ∉ s) (L : Fin m → ℝ) (η t : ℝ) :
    (signedChordNet net s p n L η t).W₂ i = net.W₂ i ∧
    (signedChordNet net s p n L η t).b₂ i = net.b₂ i := by
  have hip : i ≠ p := by rintro rfl; exact hi hp
  have hin : i ≠ n := by rintro rfl; exact hi hn
  constructor
  · funext j
    simp only [signedChordNet,interpolateSecondRows,withSecondRows,signedChordRows,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,if_neg hip,if_neg hin,if_neg hi]
    ring
  · simp only [signedChordNet,interpolateSecondRows,withSecondRows,signedChordBiases,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,if_neg hip,if_neg hin,if_neg hi]
    ring

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
