import research.sN.overnight_20261103.constants.ThetaQuadratic

/-! Independent expanded contracts for the unconditional N²/175000 theorem.
The original all-real model and literal stronger rank event are explicit. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.OvernightConstants.Theta.Check
open BigOperators Frontier Frontier.RandomRestriction
open AffineSkipExtension GrowingMatching
attribute [local instance] Classical.propDecidable

/-- Exact raw evaluator, with all original first-hidden rows counted. -/
theorem raw_nine_array_contract {N h₁ h₂ : ℕ} [NeZero N] (hN : 3≤N)
    (A : Fin h₁→Fin N→ℝ) (b : Fin h₁→ℝ)
    (W : Fin h₂→Fin h₁→ℝ) (U : Fin h₂→Fin N→ℝ)
    (θ d : Fin h₂→ℝ) (B : Fin h₁→ℝ) (L : Fin N→ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N→ℝ,
      (∑ k, d k*max 0 ((∑ j, W k j*max 0 ((∑ i, A j i*x i)+b j))+
        (∑ i, U k i*x i)+θ k))+
      ((∑ j, B j*max 0 ((∑ i, A j i*x i)+b j))+
        (∑ i, L i*x i)+β)=Maximum N x)
    (hwidth : (h₁:ℝ)≤(N:ℝ)^2) :
    (1/175000:ℝ)*(N:ℝ)^2≤(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact affine_quadratic hN net hmax hwidth

/-- Both budgets hold for the SAME actual model, with both index sets retained. -/
theorem actual_joint_half_contract {N n h₁ h₂ : ℕ} [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x, net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      16*(∑ j, (NormalizedNetwork.rowSupport (model.A j)).card.descFactorial 4)≤105*h₁ ∧
      8*(Finset.univ.filter (fun j : Fin h₁ =>
        3≤(NormalizedNetwork.rowSupport (model.A j)).card)).card≤h₁ :=
  Overnight.Constants.FallingHalf.exists_joint_model net hn hmax hpair

/-- The exact all-real five-input obstruction is proved, not hypothesized. -/
theorem five_input_obstruction (h₁ h₂ : ℕ) (net : NormalizedNetwork 5 h₁ h₂)
    (hn : net.TranslationNormalized)
    (hrows : ∀ j, (NormalizedNetwork.rowSupport (net.A j)).card≤2)
    (hmax : ∀ x, net.eval x=Maximum 5 x) :
    ∃ r : Fin h₂, HasMatchingOn (braidInteractionGraph net hn r) 2 Finset.univ :=
  localMatchingObstruction_five_two h₁ h₂ net hn hrows hmax

/-- Actual rank permutations and actual nonanchor isolated gaps. No moment
or probability hypothesis is present. The threshold is exactly 7K/10. -/
theorem actual_high_rank_event_contract (m K : ℕ) (hm : 20000≤m)
    (hK : 50≤K) (hKm : 10*K≤m) :
    ((Finset.univ.filter (fun ρ : Equiv.Perm (Fin m) =>
      ((GoodEvent.isolatedGaps (Finset.univ.filter
        (fun g : Fin m => (ρ g).val<K))).card:ℝ)<(7/10:ℝ)*(K:ℝ))).card:ℝ)/
      Fintype.card (Equiv.Perm (Fin m))≤1/16 := by
  simpa only [CherryConcentration.highBadIsolatedEvent,GoodEvent.smallRankGaps] using
    CherryConcentration.highBad_fraction_le_sixteenth hm hK hKm

private theorem actual_caterpillar_witness (N : ℕ) [NeZero N]
    (hN : 3≤N) (hwidth : firstWidth N≤N^2) :
    ∃ net : AffineSkipNetwork N (firstWidth N) (secondWidth N),
      (∀ x, AffineSkipExtension.eval net x=Maximum N x) ∧
      (firstWidth N:ℝ)≤(N:ℝ)^2 ∧
      (1/175000:ℝ)*(N:ℝ)^2≤(secondWidth N:ℝ) := by
  obtain ⟨net,hnet,_hrational,_hzeroBias⟩ := caterpillar_net N
  have hm : ∀ x, AffineSkipExtension.eval (ofOrdinary net) x=Maximum N x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hw : (firstWidth N:ℝ)≤(N:ℝ)^2 := by exact_mod_cast hwidth
  exact ⟨ofOrdinary net,hm,hw,affine_quadratic hN _ hm hw⟩

theorem smallest_arity_nonvacuity :
    ∃ net : AffineSkipNetwork 3 (firstWidth 3) (secondWidth 3),
      (∀ x, AffineSkipExtension.eval net x=Maximum 3 x) ∧
      (firstWidth 3:ℝ)≤(3:ℝ)^2 ∧
      (1/175000:ℝ)*(3:ℝ)^2≤(secondWidth 3:ℝ) := by
  apply actual_caterpillar_witness 3 (by decide)
  rw [firstWidth,Nat.choose_two_right]
  norm_num

/-- First odd dimension beyond the small-arity linear branch. -/
theorem odd_large_arity_nonvacuity :
    ∃ net : AffineSkipNetwork 50001 (firstWidth 50001) (secondWidth 50001),
      (∀ x, AffineSkipExtension.eval net x=Maximum 50001 x) ∧
      (firstWidth 50001:ℝ)≤(50001:ℝ)^2 ∧
      (1/175000:ℝ)*(50001:ℝ)^2≤(secondWidth 50001:ℝ) := by
  apply actual_caterpillar_witness 50001 (by decide)
  rw [firstWidth,Nat.choose_two_right]
  norm_num

#check @raw_nine_array_contract
#check @actual_high_rank_event_contract
#print axioms raw_nine_array_contract
#print axioms actual_joint_half_contract
#print axioms five_input_obstruction
#print axioms actual_high_rank_event_contract
#print axioms smallest_arity_nonvacuity
#print axioms odd_large_arity_nonvacuity
end MaxCaterpillar.OvernightConstants.Theta.Check
