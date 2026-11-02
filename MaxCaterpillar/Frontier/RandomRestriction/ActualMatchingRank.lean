import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingCleanFlip
import MaxCaterpillar.Frontier.RandomRestriction.MatchingColumnOrientation
import MaxCaterpillar.Frontier.RandomRestriction.MatchingRank
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Graph

/-! # Actual second-neuron survival on clean recorded-data fibers

The original nonlinear second preactivation is tested at the actual gap point.
Its coefficient vector is proved affine on each clean actual permutation fiber;
its nonzero matching columns are independent by their disjoint coordinates.
Uniformity comes from genuine permutations, not from a replacement coin model.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators Cartesian DominantGap GoodEvent NormalizedNetwork
variable {N h₁ h₂ m : ℕ}

noncomputable def tailBraidWeight (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (a b : Fin m) : ℝ :=
  braidEdgeWeight net.A (net.W k) (e a) (e b)

theorem tailBraidWeight_symm (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (e : Fin m ↪ Fin N) (k : Fin h₂)
    (a b : Fin m) : tailBraidWeight net e k a b = tailBraidWeight net e k b a :=
  braidEdgeWeight_symm net.A (net.W k) hn.1 (e a) (e b)

noncomputable def activeMatchingEdges (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho : Equiv.Perm (Fin m)) (K : ℕ)
    (tau : Equiv.Perm (Fin m)) : Finset (↥(rankIsolatedGaps rho K)) := by
  classical
  exact Finset.univ.filter fun g => tailBraidWeight net e k
    (tau (isolatedGapPredecessor g.val)) (tau g.val) ≠ 0

lemma neg_rawColumn_eq_root {ι : Type*} [Fintype ι] [DecidableEq ι]
    (slot : (ι × Bool) ↪ Fin m) (E : Fin m → Fin m → ℝ)
    (tau : Equiv.Perm (Fin m)) (i : ι) :
    -Matching.rawColumn slot E tau i =
      E (tau (slot (i,false))) (tau (slot (i,true))) •
        braidRoot (tau (slot (i,false))) (tau (slot (i,true))) := by
  funext x
  simp [Matching.rawColumn,matchingRoot,braidRoot,unitVec]

theorem actualMatchingRow_fiber_flip
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho : Equiv.Perm (Fin m)) (K : ℕ)
    (u : Matching.Data (↥(rankIsolatedGaps rho K)) m)
    (base p : Matching.Fiber (rankIsolatedSlots rho K) u)
    (hclean : ActualClean net e k rho K base.val)
    (T : ℝ) (hT : 0 < T)
    (hgeneric : ∀ tau, GenericNetworkPoint net e (tau,rho) T)
    (g : ↥(rankIsolatedGaps rho K)) :
    actualMatchingRow net e k rho (Matching.fiberFlip (rankIsolatedSlots rho K) u g p).val T -
      actualMatchingRow net e k rho p.val T =
      (coinCoefficient (!(Matching.fiberCoins (rankIsolatedSlots rho K) u p g)) -
        coinCoefficient (Matching.fiberCoins (rankIsolatedSlots rho K) u p g)) •
        Matching.canonicalColumn (rankIsolatedSlots rho K) (tailBraidWeight net e k) base g := by
  have hpclean := (actualClean_constant_on_fiber net hn e k rho K u base p).mp hclean
  have hf := actualMatchingRow_swap net hn e k rho p.val K g T hT
    (hgeneric p.val) (hgeneric _) hpclean
  have hr := neg_rawColumn_eq_root (rankIsolatedSlots rho K) (tailBraidWeight net e k) p.val g
  change -Matching.rawColumn (rankIsolatedSlots rho K) (tailBraidWeight net e k) p.val g =
    braidEdgeWeight net.A (net.W k)
      (e (p.val (isolatedGapPredecessor g.val))) (e (p.val g.val)) •
        braidRoot (p.val (isolatedGapPredecessor g.val)) (p.val g.val) at hr
  change actualMatchingRow net e k rho (Matching.swapTau (rankIsolatedSlots rho K) g p.val) T -
    actualMatchingRow net e k rho p.val T = _
  rw [hf, ←hr]
  exact Matching.neg_rawColumn_eq_coin_difference (rankIsolatedSlots rho K)
    (tailBraidWeight net e k) (tailBraidWeight_symm net hn e k) u base p g

/-- Conditional survival of the actual second preactivation, with the rank
counting exactly the nonzero original signed edge weights in this matching.
The sole cleanliness premise is the literal original-row dominant-gap event. -/
theorem actualClean_fiber_survival_fraction_le
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho : Equiv.Perm (Fin m)) (K : ℕ)
    (u : Matching.Data (↥(rankIsolatedGaps rho K)) m)
    (base : Matching.Fiber (rankIsolatedSlots rho K) u)
    (hclean : ActualClean net e k rho K base.val)
    (T : ℝ) (hT : 0 < T)
    (hgeneric : ∀ tau, GenericNetworkPoint net e (tau,rho) T) :
    ((Finset.univ.filter (fun p : Matching.Fiber (rankIsolatedSlots rho K) u =>
        net.inner k (actualGapPoint e (p.val,rho) T) = 0)).card : ℝ) /
      Fintype.card (Matching.Fiber (rankIsolatedSlots rho K) u) ≤
        (1/2 : ℝ) ^ (activeMatchingEdges net e k rho K base.val).card := by
  classical
  let slot := rankIsolatedSlots rho K
  let F : Matching.Fiber slot u → Point m := fun p => actualMatchingRow net e k rho p.val T
  let cols := Matching.canonicalColumn slot (tailBraidWeight net e k) base
  let s := activeMatchingEdges net e k rho K base.val
  have hind : LinearIndependent ℝ (fun i : s => cols i.val) := by
    apply Matching.canonicalColumns_on_independent slot (tailBraidWeight net e k) base s
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hchange : ∀ i p, F (Matching.fiberFlip slot u i p) - F p =
      (coinCoefficient (!(Matching.fiberCoins slot u p i)) -
        coinCoefficient (Matching.fiberCoins slot u p i)) • cols i :=
    fun i p => actualMatchingRow_fiber_flip net hn e k rho K u base p hclean T hT hgeneric i
  have hc := Matching.value_solution_fraction_le slot u F cols base hchange 0 s hind
  have he : Matching.valueSolutions slot u F 0 =
      Finset.univ.filter (fun p : Matching.Fiber slot u =>
        net.inner k (actualGapPoint e (p.val,rho) T) = 0) := by
    ext p
    simpa [Matching.valueSolutions, F] using
      actualMatchingRow_zero_iff net e k rho p.val T (hgeneric p.val)
  rw [he] at hc
  simpa only [one_div_pow] using hc

#print axioms actualMatchingRow_fiber_flip
#print axioms actualClean_fiber_survival_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction
