import MaxCaterpillar.Frontier.RandomRestriction.FeedingWidthExtension
import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension

/-! Independent contracts for the two scope extensions. -/
set_option autoImplicit false
noncomputable section
namespace WidthExtensionsCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open FeedingWidthExtension AffineSkipExtension
attribute [local instance] Classical.propDecidable

example {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) :
    feedingCount net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,net.W₂ k j≠0} := by
  unfold feedingCount
  exact Fintype.card_congr (Equiv.refl _)

example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N) (net : Network N h₁ h₂)
    (hnet : ∀ x,net.eval x=Maximum N x) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2)
      ((N : ℝ)^4/(Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,net.W₂ k j≠0} : ℝ))≤(h₂ : ℝ) := by
  have hc : feedingCount net=Fintype.card {j : Fin h₁ // ∃ k : Fin h₂,net.W₂ k j≠0} := by
    unfold feedingCount
    exact Fintype.card_congr (Equiv.refl _)
  simpa only [hc] using second_width_tradeoff_feeding hN net hnet

example {N h₁ h₂ : ℕ} (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    (encode net : Network N (h₁+N+N) (h₂+2)).eval x=eval net x := encode_eval net x

-- This is the fully affine formula from Jensen's model, expanded into its
-- nine unrestricted parameter arrays/scalars. No feeding, bias, support,
-- normalization or coefficient premise is supplied.
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N)
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k,d k*max 0 ((∑ j,W k j*max 0 ((∑ i,A j i*x i)+b j))+
        (∑ i,U k i*x i)+θ k))+
      ((∑ j,B j*max 0 ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x) :
    (1/1600000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact second_width_tradeoff_affine_skips_unshifted hN net hmax

-- The extended hypotheses are satisfiable at their exact boundary arity.
example : ∃ net : AffineSkipNetwork 1040 (firstWidth 1040) (secondWidth 1040),
    (∀ x,eval net x=Maximum 1040 x) ∧
    (1/1600000000 : ℝ)*min ((1040 : ℝ)^2)
      ((1040 : ℝ)^4/(firstWidth 1040 : ℝ))≤(secondWidth 1040 : ℝ) := by
  obtain ⟨net,hnet,_hbias,_hrational⟩ := caterpillar_net 1040
  have hm : ∀ x,eval (ofOrdinary net) x=Maximum 1040 x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  exact ⟨ofOrdinary net,hm,second_width_tradeoff_affine_skips_unshifted (by decide) _ hm⟩

#check @second_width_tradeoff_feeding
#check @second_width_quadratic_feeding
#check @second_width_tradeoff_affine_skips
#check @second_width_tradeoff_affine_skips_unshifted
#print axioms prune_eval
#print axioms second_width_tradeoff_feeding
#print axioms second_width_quadratic_feeding
#print axioms encode_eval
#print axioms second_width_tradeoff_affine_skips
#print axioms second_width_tradeoff_affine_skips_unshifted
end WidthExtensionsCheck
