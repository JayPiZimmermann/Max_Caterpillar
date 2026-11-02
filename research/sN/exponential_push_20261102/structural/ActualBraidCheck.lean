import research.sN.exponential_push_20261102.structural.ActualBraidGraph

set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.ActualBraid.IndependentCheck
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N h₁ h₂ : ℕ}

/-- Expanded all-arity actual-inner contract. -/
example (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hs : ∀ j,(rowSupport (net.A j)).card≤2) (k : Fin h₂) (x : Point N) :
    net.inner k x=lin (head (net.U k) net.A (net.W k)) x+
      ∑ p in activeEdges net.A (net.W k),
        coefficient net.A (net.W k) p*relu (x (left p)-x (right p)) :=
  linear_combination_active (net.U k) net.A (net.W k) hn.1 hs x

/-- Expanded output contract, including every original skip and outer slot. -/
example (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hs : ∀ j,(rowSupport (net.A j)).card≤2) (x : Point N) :
    net.eval x=
      lin (head net.L net.A net.B) x+
      (∑ p : Pair N,coefficient net.A net.B p*relu (x (left p)-x (right p)))+
      ∑ k,net.d k*relu (lin (head (net.U k) net.A (net.W k)) x+
        ∑ p : Pair N,coefficient net.A (net.W k) p*relu (x (left p)-x (right p))) :=
  eval_eq_canonical net hn hs x

/-- Two opposite original rows cancel in the aggregated nonlinear coefficient,
even though their actual signed ReLU combination has a nonzero linear head. -/
theorem opposite_coefficient (v : Point N) (p : Pair N) :
    coefficient ![v,-v] ![1,-1] p=0 := by
  have hs : rowSupport (-v)=rowSupport v := by
    classical
    ext i
    simp only [mem_rowSupport,Pi.neg_apply,neg_ne_zero]
  simp [coefficient,Fin.sum_univ_succ,rowAbsCoefficient,hs,abs_neg]
  split_ifs <;> ring

example (v : Point N) (x : Point N) :
    relu (lin v x)-relu (lin (-v) x)=lin v x := by
  rw [lin_neg_left]
  exact relu_sub_relu_neg _

/-- Nonvacuity at the N=1 boundary, with nonzero feeding and output skips. -/
noncomputable def oneModel : NormalizedNetwork 1 1 1 where
  A := fun _ => 0
  U := fun _ => 0
  W := fun _ _ => 37
  L := fun _ => 1
  B := fun _ => -5
  d := fun _ => 11

example : oneModel.TranslationNormalized := by
  simp [TranslationNormalized,oneModel,Fin.sum_univ_succ]

example (x : Point 1) : oneModel.eval x=x 0 := by
  simp [NormalizedNetwork.eval,NormalizedNetwork.inner,oneModel,lin,
    Fin.sum_univ_succ,relu]

#print axioms MaxCaterpillar.ExponentialPush.ActualBraid.linear_combination_canonical
#print axioms MaxCaterpillar.ExponentialPush.ActualBraid.coefficient_eq_original
#print axioms MaxCaterpillar.ExponentialPush.ActualBraid.head_sum
#print axioms MaxCaterpillar.ExponentialPush.ActualBraid.eval_eq_canonical
#print axioms MaxCaterpillar.ExponentialPush.ActualBraid.active_indexedGraph_eq
#print axioms opposite_coefficient
end MaxCaterpillar.ExponentialPush.ActualBraid.IndependentCheck
