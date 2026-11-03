import research.sN.max5_optimal_20261103.lower.endpoint_contact.EndpointContact
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Max5Optimal.TripleContact MaxCaterpillar.Max5Optimal.EndpointContact

example : ∀ {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (βg cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (βh ch : Fin mh → ℝ),
    (∀ x, shallow aR bR AR βR cR x+
      relu (shallow ag bg Ag βg cg x)+relu (shallow ah bh Ah βh ch x)=Maximum 5 x) →
    ∀ (i j : Fin 5), i≠j →
    shallow ag bg Ag βg cg (-unitVec i)=0 →
    shallow ah bh Ah βh ch (-unitVec i)=0 →
    directionalSlope ag Ag βg cg (-unitVec i) (-unitVec j)=0 ∨
      directionalSlope ah Ah βh ch (-unitVec i) (-unitVec j)=0 :=
  @shared_endpoint_directional_disjunction

/-- The checked consumer exposes the exact literal branch expression used
by arithmetic models, rather than only referring to endpointSlope. -/
example : ∀ {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (ch : Fin mh → ℝ),
    (∀ x, shallow aR bR AR βR cR x+
      relu (shallow ag bg Ag 0 cg x)+relu (shallow ah bh Ah 0 ch x)=Maximum 5 x) →
    ∀ (i j : Fin 5), i≠j →
    shallow ag bg Ag 0 cg (-unitVec i)=0 →
    shallow ah bh Ah 0 ch (-unitVec i)=0 →
    (-ag j+∑ k, cg k*(if Ag k i<0 then -Ag k j
      else if Ag k i=0 then max 0 (-Ag k j) else 0))=0 ∨
    (-ah j+∑ k, ch k*(if Ah k i<0 then -Ah k j
      else if Ah k i=0 then max 0 (-Ah k j) else 0))=0 :=
  @shared_endpoint_slope_disjunction

#print axioms shared_endpoint_directional_disjunction
#print axioms shared_endpoint_slope_disjunction
