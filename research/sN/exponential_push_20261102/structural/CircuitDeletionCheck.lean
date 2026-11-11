import research.sN.exponential_push_20261102.structural.CircuitDeletion

set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.IndependentCheck
open BigOperators

/-- Expanded contract: no sampled signs, positivity of coefficients, ReLU-only
outer hypothesis, or convexity assumption is hidden in circuit deletion. -/
example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (ell weights : ι → ℝ) (baseline : ℝ) (outer : ℝ → ℝ)
    (nonempty : S.Nonempty) (balance : ∑ i in S, ell i = 0) :
    outer (baseline + ∑ i in S, weights i * max (ell i) 0) =
      - ∑ T in S.powerset.erase S, (-1 : ℝ) ^ (S \ T).card *
        outer (baseline + ∑ i in T, weights i * max (ell i) 0) :=
  circuit_deletion S ell weights baseline outer nonempty balance

/-- Nonvacuity with arbitrary real inputs and the genuine cyclic differences. -/
example (x y z a : ℝ) (c : Fin 3 → ℝ) (F : ℝ → ℝ) :
    F (a + ∑ i : Fin 3, c i * max (![x-y,y-z,z-x] i) 0) =
      - ∑ T in (Finset.univ : Finset (Fin 3)).powerset.erase Finset.univ,
        (-1 : ℝ) ^ (Finset.univ \ T).card *
        F (a + ∑ i in T, c i * max (![x-y,y-z,z-x] i) 0) := by
  apply circuit_deletion
  · exact Finset.univ_nonempty
  · norm_num [Fin.sum_univ_succ]

#print axioms MaxCaterpillar.ExponentialPush.circuit_deletion
end MaxCaterpillar.ExponentialPush.IndependentCheck
