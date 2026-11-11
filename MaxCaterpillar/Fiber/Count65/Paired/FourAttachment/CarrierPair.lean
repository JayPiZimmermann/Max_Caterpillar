import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # A nonnegative carrier and a signed pair attach by a physical chord

This is a continuous path of ordinary five-slot network parameters. The
carrier, signed pair, and two comparison orientations move simultaneously.
The signed-pair coefficient may have either sign and need not be normalized.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m : ℕ}

noncomputable def carrierPairNet (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D : Fin m → ℝ) (γ η δ θ d K s : ℝ) : Network N m 5 where
  W₁ := A
  b₁ := β
  W₂ := ![g,H,-H,D,-D]
  b₂ := ![γ,η,-η,δ,-δ]
  w₃ := ![d,K,-K,1-s,s]
  b₃ := θ

lemma carrierPairNet_eval (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D : Fin m → ℝ) (γ η δ θ d K s : ℝ) (x : Point N)
    (hg : 0 ≤ preact A β g γ x) :
    (carrierPairNet A β g H D γ η δ θ d K s).eval x =
      d*preact A β g γ x+K*preact A β H η x+
        relu (preact A β D δ x)-s*preact A β D δ x+θ := by
  simp only [Network.eval,carrierPairNet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    add_zero]
  change d*relu (preact A β g γ x)+(K*relu (preact A β H η x)+
    ((-K)*relu (preact A β (-H) (-η) x)+
      ((1-s)*relu (preact A β D δ x)+s*relu (preact A β (-D) (-δ) x))))+θ = _
  have hnH : preact A β (-H) (-η) x = -preact A β H η x :=
    preact_neg A β H η x
  have hnD : preact A β (-D) (-δ) x = -preact A β D δ x :=
    preact_neg A β D δ x
  rw [hnH,hnD,relu_of_nonneg hg]
  have hH := relu_sub_relu_neg (preact A β H η x)
  have hD := relu_sub_relu_neg (preact A β D δ x)
  linear_combination K*hH-s*hD

/-- Simultaneously contract the carrier and the second comparison orientation.
At the endpoint only slots 1, 2, and 3 can contribute. -/
noncomputable def carrierPairChord (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s t : ℝ) : Network N m 5 :=
  carrierPairNet A β ((1-t) • g) ((1-t) • H+t • (K⁻¹ • B)) D
    ((1-t)*γ) ((1-t)*η+t*(ζ/K)) δ θ d K ((1-t)*s)

lemma preact_smul (A : Fin m → Point N) (β V : Fin m → ℝ)
    (v c : ℝ) (x : Point N) :
    preact A β (c • V) (c*v) x = c*preact A β V v x := by
  simp only [preact,Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  ring

lemma preact_chord (A : Fin m → Point N) (β H B : Fin m → ℝ)
    (η ζ K t : ℝ) (x : Point N) :
    preact A β ((1-t) • H+t • (K⁻¹ • B)) ((1-t)*η+t*(ζ/K)) x =
      (1-t)*preact A β H η x+t*(preact A β B ζ x/K) := by
  simp only [preact,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,div_eq_mul_inv]
  ring

lemma carrierPairChord_zero (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) :
    carrierPairChord A β g H D B γ η δ ζ θ d K s 0=
      carrierPairNet A β g H D γ η δ θ d K s := by
  simp [carrierPairChord]

lemma carrierPairChord_eval (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) (hK : K≠0)
    (hg : ∀ x, 0≤preact A β g γ x)
    (hfit : ∀ x, d*preact A β g γ x+K*preact A β H η x-
      s*preact A β D δ x=preact A β B ζ x)
    (t : ℝ) (ht : t≤1) (x : Point N) :
    (carrierPairChord A β g H D B γ η δ ζ θ d K s t).eval x=
      (carrierPairNet A β g H D γ η δ θ d K s).eval x := by
  have hg' : 0≤preact A β ((1-t) • g) ((1-t)*γ) x := by
    rw [preact_smul]
    exact mul_nonneg (sub_nonneg.mpr ht) (hg x)
  rw [carrierPairChord,carrierPairNet_eval _ _ _ _ _ _ _ _ _ _ _ _ x hg',
    carrierPairNet_eval _ _ _ _ _ _ _ _ _ _ _ _ x (hg x),preact_smul,preact_chord]
  have hf := hfit x
  have hdiv : K*(preact A β B ζ x/K)=preact A β B ζ x := by
    field_simp [hK]
    ring
  linear_combination -t*hf+t*hdiv

theorem continuous_carrierPairChord (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) :
    Continuous (carrierPairChord A β g H D B γ η δ ζ θ d K s) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,?_,continuous_const⟩
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> simp only [carrierPairChord,carrierPairNet,Pi.add_apply,
      Pi.smul_apply,smul_eq_mul,Pi.neg_apply,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro i
    fin_cases i <;> simp only [carrierPairChord,carrierPairNet,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro i
    fin_cases i <;> simp only [carrierPairChord,carrierPairNet,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity

/-- An actual five-slot exact completion in carrier/pair/comparator form has
an exact parameter path to a network supported on three slots. `hfit` is an
ordinary affine identity on natural first-layer features. -/
theorem carrierPairChord_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) (hK : K≠0)
    (hg : ∀ x, 0≤preact A β g γ x)
    (hfit : ∀ x, d*preact A β g γ x+K*preact A β H η x-
      s*preact A β D δ x=preact A β B ζ x)
    (hexact : ∀ x, (carrierPairNet A β g H D γ η δ θ d K s).eval x=Maximum N x) :
    JoinedIn (ExactSet N m 5) (carrierPairNet A β g H D γ η δ θ d K s)
      (carrierPairChord A β g H D B γ η δ ζ θ d K s 1) := by
  apply JoinedIn.ofLine
    (continuous_carrierPairChord A β g H D B γ η δ ζ θ d K s).continuousOn
    (carrierPairChord_zero A β g H D B γ η δ ζ θ d K s) rfl
  rintro _ ⟨t,ht,rfl⟩ x
  rw [carrierPairChord_eval A β g H D B γ η δ ζ θ d K s hK hg hfit t ht.2 x]
  exact hexact x

/-- Exactness itself recovers the affine fit used by the physical chord. -/
theorem carrierPair_fit_of_exact [NeZero N] (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ)
    (hg : ∀ x, 0≤preact A β g γ x)
    (hexact : ∀ x, (carrierPairNet A β g H D γ η δ θ d K s).eval x=Maximum N x)
    (hmax : ∀ x, Maximum N x=preact A β B ζ x+relu (preact A β D δ x)+θ) :
    ∀ x, d*preact A β g γ x+K*preact A β H η x-
      s*preact A β D δ x=preact A β B ζ x := by
  intro x
  have h := hexact x
  rw [carrierPairNet_eval _ _ _ _ _ _ _ _ _ _ _ _ x (hg x),hmax x] at h
  linarith only [h]

lemma carrierPairChord_one_unused (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) :
    (carrierPairChord A β g H D B γ η δ ζ θ d K s 1).W₂ 0=0 ∧
    (carrierPairChord A β g H D B γ η δ ζ θ d K s 1).b₂ 0=0 ∧
    (carrierPairChord A β g H D B γ η δ ζ θ d K s 1).w₃ 4=0 := by
  refine ⟨?_,?_,?_⟩
  · change (1-(1:ℝ)) • g=0
    simp
  · change (1-(1:ℝ))*γ=0
    ring
  · change (1-(1:ℝ))*s=0
    ring

/-- A negative diagonal baseline forces a genuine nonzero signed pair.
This rules out vanishing orientation totals after the common-support merge. -/
theorem carrierPair_coefficient_ne_zero (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ d K s : ℝ) (hd : 0≤d)
    (hg : ∀ x, 0≤preact A β g γ x)
    (hfit : ∀ x, d*preact A β g γ x+K*preact A β H η x-
      s*preact A β D δ x=preact A β B ζ x)
    (x₀ : Point N) (hD : preact A β D δ x₀=0)
    (hB : preact A β B ζ x₀<0) : K≠0 := by
  intro hK
  have hf := hfit x₀
  rw [hK,hD,zero_mul,mul_zero,add_zero,sub_zero] at hf
  have hp := mul_nonneg hd (hg x₀)
  rw [hf] at hp
  exact (not_lt.mpr hp) hB

/-- All-input exactness, nonnegativity of the physical carrier, and a negative
baseline probe suffice for the actual attachment chord. There is no atom
identity, normalization path, or attachment hypothesis in this interface. -/
theorem carrierPair_attaches [NeZero N]
    (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) (hd : 0≤d)
    (hg : ∀ x, 0≤preact A β g γ x)
    (hexact : ∀ x, (carrierPairNet A β g H D γ η δ θ d K s).eval x=Maximum N x)
    (hmax : ∀ x, Maximum N x=preact A β B ζ x+relu (preact A β D δ x)+θ)
    (x₀ : Point N) (hD : preact A β D δ x₀=0)
    (hB : preact A β B ζ x₀<0) :
    JoinedIn (ExactSet N m 5) (carrierPairNet A β g H D γ η δ θ d K s)
      (carrierPairChord A β g H D B γ η δ ζ θ d K s 1) := by
  have hf := carrierPair_fit_of_exact A β g H D B γ η δ ζ θ d K s hg hexact hmax
  have hK := carrierPair_coefficient_ne_zero A β g H D B γ η δ ζ d K s hd hg hf x₀ hD hB
  exact carrierPairChord_joinedIn_exact A β g H D B γ η δ ζ θ d K s hK hg hf hexact

lemma carrierPairChord_one_support (A : Fin m → Point N) (β : Fin m → ℝ)
    (g H D B : Fin m → ℝ) (γ η δ ζ θ d K s : ℝ) :
    ∀ i : Fin 5, i∉({1,2,3} : Finset (Fin 5)) →
      (carrierPairChord A β g H D B γ η δ ζ θ d K s 1).w₃ i=0 ∨
      ((carrierPairChord A β g H D B γ η δ ζ θ d K s 1).W₂ i=0 ∧
       (carrierPairChord A β g H D B γ η δ ζ θ d K s 1).b₂ i=0) := by
  intro i hi
  have hu := carrierPairChord_one_unused A β g H D B γ η δ ζ θ d K s
  fin_cases i
  · exact Or.inr ⟨hu.1,hu.2.1⟩
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact Or.inl hu.2.2

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
