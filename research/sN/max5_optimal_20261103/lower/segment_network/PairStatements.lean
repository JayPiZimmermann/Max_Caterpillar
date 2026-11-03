import research.sN.max5_optimal_20261103.lower.segment_network.SegmentNetworkPairs
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.SegmentNetwork
open BigOperators Frontier TripleContact

example : ∀ {m mR : ℕ}
    (A : Fin m → Point 5) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Point 5) (bR : ℝ) (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (i j : Fin 5), i≠j →
    (∀ l, l≠k → A l i=0 ∨ A l j=0 ∨ A l i+A l j=0) →
    core A c (-unitVec i)=0 → core A c (-unitVec j)=0 →
    core A d (-unitVec i)=0 → core A d (-unitVec j)=0 →
    (∀ x, shallow aR bR AR βR cR x+
      relu (core A c x)+relu (core A d x)=Maximum 5 x) →
    pairMidpointMass A c k i j=0 ∨ pairMidpointMass A d k i j=0 ∨ A k i+A k j=0 :=
  @balance_or_zero_pair_mass

/-- Literal arrays and arbitrary distinct contact labels. -/
example {m mR : ℕ}
    (A : Fin m → Fin 5 → ℝ) (c d : Fin m → ℝ) (k : Fin m)
    (aR : Fin 5 → ℝ) (bR : ℝ) (AR : Fin mR → Fin 5 → ℝ) (βR cR : Fin mR → ℝ)
    (i j : Fin 5) (hij : i≠j)
    (hrows : ∀ l, l≠k → A l i=0 ∨ A l j=0 ∨ A l i+A l j=0)
    (hci : (∑ l, c l*max 0 (-A l i))=0)
    (hcj : (∑ l, c l*max 0 (-A l j))=0)
    (hdi : (∑ l, d l*max 0 (-A l i))=0)
    (hdj : (∑ l, d l*max 0 (-A l j))=0)
    (heq : ∀ x : Fin 5 → ℝ,
      (∑ s, aR s*x s)+bR+(∑ l, cR l*max 0 ((∑ s, AR l s*x s)+βR l))+
      max 0 (∑ l, c l*max 0 (∑ s, A l s*x s))+
      max 0 (∑ l, d l*max 0 (∑ s, A l s*x s))=Maximum 5 x) :
    (∑ l in Finset.univ.erase k, c l*(if A l i+A l j=0 then |A l i| else 0))=0 ∨
    (∑ l in Finset.univ.erase k, d l*(if A l i+A l j=0 then |A l i| else 0))=0 ∨
    A k i+A k j=0 := by
  apply balance_or_zero_pair_mass A c d k aR bR AR βR cR i j hij hrows
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hci
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hcj
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hdi
  · simpa only [core,lin_neg_right,lin_unitVec,relu] using hdj
  · simpa only [shallow,core,lin,relu] using heq

#check @balance_or_zero_pair_mass
#print axioms balance_or_zero_pair_mass
end MaxCaterpillar.Max5Optimal.SegmentNetwork
