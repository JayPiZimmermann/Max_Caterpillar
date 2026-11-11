import MaxCaterpillar.Frontier.StarCertificate.StarObstruction

set_option autoImplicit false
open MaxCaterpillar MaxCaterpillar.Frontier MaxCaterpillar.Frontier.StarCertificate BigOperators

example : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
    evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0 :=
  starAnova_all_real

example : ∀ (c : Fin 5) (v v' : Fin 5 → ℝ),
    (∑ e : Equiv.Perm (Fin 5),
      starXi (permutationFunctionChain (starAtSetFunction c v v') e)) = 0 :=
  starAt_permutation_sum_eq_zero

example {ι : Type*} [Fintype ι]
    (center : ι → Fin 5) (v v' : ι → Fin 5 → ℝ) (weights : ι → ℝ)
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0 < x j) →
        lin l x + β = ∑ i, weights i * relu
          (lin (setFunctionChain (starAtSetFunction (center i) (v i) (v' i)) p) x)) :
    topMobius (fun B => (∑ i, weights i * relu (starAtSetFunction (center i) (v i) (v' i) B)) +
      booleanQuadratic a b d B) = 0 :=
  star_network_booleanQuadratic_topMobius_zero center v v' weights a b d hchamber

/-- The gluing premise is satisfiable; it is not an inconsistent substitute
for the obstruction. One zero star already gives the zero chamber function. -/
example : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
    ∀ x : Point 4, (∀ j, 0 < x j) →
      lin l x + β = ∑ _i : Fin 1, (1 : ℝ) * relu
        (lin (setFunctionChain (starAtSetFunction 0 0 0) p) x) := by
  intro p
  refine ⟨0,0,?_⟩
  intro x _
  simp [lin,setFunctionChain,starAtSetFunction,relu]

#check @starAnova_all_real
#check @starAt_permutation_sum_eq_zero
#check @star_network_topMobius_zero
#check @star_network_booleanQuadratic_topMobius_zero
#check @star_network_booleanQuadratic_not_booleanOR
#print axioms starAnova_all_real
#print axioms starAt_permutation_sum_eq_zero
#print axioms star_network_topMobius_zero
#print axioms star_network_booleanQuadratic_topMobius_zero
#print axioms star_network_booleanQuadratic_not_booleanOR
