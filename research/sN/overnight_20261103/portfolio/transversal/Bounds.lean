import research.sN.overnight_20261103.portfolio.transversal.Model
import MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BraidCorollary
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.SetRestriction

/-! Unconditional quadratic and conditional growing-matching bounds after
removing a transversal of the non-braid first-row support hypergraph. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.SupportTransversal
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork AffineSkipExtension GrowingMatching
variable {N m h₁ h₂ : ℕ}

/-- Arbitrarily many braid first rows are allowed. The fixed five-input
obstruction is already proved in the imported production closure. -/
theorem normalized_braid_quadratic [NeZero N] (hN : 3 ≤ N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x = Maximum N x)
    (hbraid : ∀ j, (rowSupport (net.A j)).card ≤ 2) :
    (N:ℝ)^2 / 3000000 ≤ (h₂:ℝ) := by
  have hNr : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hlinear : (N:ℝ) ≤ 2*(h₂:ℝ)+2 := by
    exact_mod_cast FeedingCore.normalized_linear_bound net hnet
  by_cases hsmall : N ≤ 25000
  · have hsmallR : (N:ℝ) ≤ 25000 := by exact_mod_cast hsmall
    have hsq := mul_le_mul_of_nonneg_left hsmallR (Nat.cast_nonneg (α:=ℝ) N)
    nlinarith only [hsq, hlinear, hNr]
  · have hbig : 25000 ≤ N := le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨m, rfl⟩ : ∃ m, N = m+5 :=
      ⟨N-5, (Nat.sub_add_cancel ((by decide : 5≤25000).trans hbig)).symm⟩
    have hm : 20000 ≤ m := by linarith only [hbig]
    have hM := BraidCorollary.largeSupportCount_eq_zero (firstSupports net) hbraid
    have hL := BraidCorollary.support_descFactorial_four_sum_eq_zero
      (firstSupports net) hbraid
    have hb := QuadraticCutoff.model_bound hm net hn hnet
      (by change (GrowingMatching.BadFirst.largeSupportCount (firstSupports net):ℝ) ≤ _
          rw [hM, Nat.cast_zero]; positivity)
      (by rw [hL]; positivity)
    have hmR : (20000:ℝ) ≤ m := by exact_mod_cast hm
    have hscale : 10*((m:ℝ)+5) ≤ 11*(m:ℝ) := by linarith only [hmR]
    have hsquare := mul_self_le_mul_self
      (by positivity : (0:ℝ) ≤ 10*((m:ℝ)+5)) hscale
    push_cast
    nlinarith only [hb, hsquare, sq_nonneg (m:ℝ)]

/-- A support transversal gives an unconditional quadratic lower bound in
the number of retained coordinates, with no assumption on first hidden width. -/
theorem affine_retained_quadratic [NeZero N] [NeZero m] (hm : 3 ≤ m)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (e : Fin m ↪ Fin N) (hkeep : BraidOnRetained net e) :
    (m:ℝ)^2 / 3000000 ≤ (h₂:ℝ) := by
  obtain ⟨model, hmax, hnorm, hbraid, _⟩ := exists_braid_model net hnet e hkeep
  exact normalized_braid_quadratic hm model hnorm hmax hbraid

/-- The only unproved input is the displayed local matching obstruction.
The selected braid model and its unchanged second width are derived here. -/
theorem conditional_affine_retained_lower_bound [NeZero N]
    (q : ℕ) (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ m)
    (H : LocalMatchingObstruction (Parameters.braidArity q) q)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (e : Fin m ↪ Fin N) (hkeep : BraidOnRetained net e) :
    (23/25:ℝ)*4^q ≤ (h₂:ℝ) := by
  letI : NeZero m := BraidCorollary.braidDimension_neZero m q hq hsize
  obtain ⟨model, hmax, hnorm, hbraid, _⟩ := exists_braid_model net hnet e hkeep
  exact BraidCorollary.conditional_braid_integer_q_lower_bound
    q hq hsize H model hnorm hmax hbraid

/-- Literal N minus transversal-size form. The complement embedding and its
nonzero dimension are constructed, rather than assumed. -/
theorem affine_transversal_quadratic [NeZero N]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (C : Finset (Fin N)) (hremain : 3 ≤ N-C.card)
    (hhit : ∀ j, net.b j=0 → (∑ i, net.A j i)=0 →
      3 ≤ (rowSupport (net.A j)).card →
      ∃ i ∈ rowSupport (net.A j), i ∈ C) :
    ((N-C.card:ℕ):ℝ)^2 / 3000000 ≤ (h₂:ℝ) := by
  classical
  let S := Cᶜ
  have hcard : S.card = N-C.card := by
    change (Finset.univ \ C).card = N-C.card
    rw [Finset.card_sdiff (Finset.subset_univ C), Finset.card_univ, Fintype.card_fin]
  have hS : 3 ≤ S.card := hcard.symm ▸ hremain
  letI : NeZero S.card := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hS)⟩
  have havoid : ∀ a, selectedEmbedding S a ∉ C := by
    intro a
    exact Finset.mem_compl.mp (S.equivFin.symm a).property
  have hkeep := braidOnRetained_of_transversal net (selectedEmbedding S) C havoid hhit
  have hb := affine_retained_quadratic hS net hnet (selectedEmbedding S) hkeep
  simpa only [hcard] using hb

#check @normalized_braid_quadratic
#check @affine_retained_quadratic
#check @conditional_affine_retained_lower_bound
#check @affine_transversal_quadratic
#print axioms normalized_braid_quadratic
#print axioms affine_retained_quadratic
#print axioms conditional_affine_retained_lower_bound
#print axioms affine_transversal_quadratic
end MaxCaterpillar.Overnight.SupportTransversal
