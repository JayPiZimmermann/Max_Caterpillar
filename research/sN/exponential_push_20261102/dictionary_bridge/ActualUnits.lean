import research.sN.exponential_push_20261102.dictionary_bridge.Expansion
import research.sN.exponential_push_20261102.structural.ActualBraidGraph

/-! Actual arbitrary-arity normalized braid neurons are exact finite sums
of forest neurons, with the original signed parallel-row cancellations.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DictionaryBridge
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ActualBraid
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

def initialState (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) (p : Pair N) : State :=
  if coefficient net.A (net.W k) p=0 then 0 else 2

@[simp] theorem active_initialState (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) :
    active (initialState net k)=activeEdges net.A (net.W k) := by
  ext p
  by_cases hp : coefficient net.A (net.W k) p=0 <;>
    simp [active,initialState,activeEdges,hp]

abbrev UnitState (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) :=
  ForestState (activeEdges net.A (net.W k)) left right

def correctedHead (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) : Point N :=
  head (net.U k) net.A (net.W k)

def stateHead (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) (s : Pair N→State) : Point N :=
  correctedHead net k+∑ p : Pair N,
    if s p=1 then coefficient net.A (net.W k) p • braidRoot (left p) (right p) else 0

def stateWeight (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (s : Pair N→State) (p : Pair N) : ℝ :=
  if s p=2 then coefficient net.A (net.W k) p else 0

lemma state_value_split (s : State) (c z : ℝ) :
    (if s=1 then c*z else 0)+(if s=2 then c*relu z else 0)=c*value s z := by
  have h01 : (0:State)≠1 := by decide
  have h10 : (1:State)≠0 := by decide
  fin_cases s
  · simp [value,h01,h10,MaxCaterpillar.relu,max_comm]
  · simp [value,h01,h10,MaxCaterpillar.relu,max_comm]
  · change (if (2:State)=1 then c*z else 0)+
      (if (2:State)=2 then c*relu z else 0)=c*value (2:State) z
    simp [value,MaxCaterpillar.relu,max_comm]

lemma lin_stateHead (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (s : Pair N→State) (x : Point N) :
    lin (stateHead net k s) x=lin (correctedHead net k) x+
      ∑ p : Pair N,if s p=1 then coefficient net.A (net.W k) p*(x (left p)-x (right p)) else 0 := by
  unfold stateHead
  rw [lin_add_left,lin_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : s p=1 <;> simp [hp,lin_smul_left,lin_zero_left,lin_root]

/-- An actual new preactivation realizes the original three-state argument,
including every linearized edge in its zero-sum linear skip. -/
theorem state_argument_realization (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂)
    (s : Pair N→State) (x : Point N) :
    lin (stateHead net k s) x+
      (∑ p : Pair N,stateWeight net k s p*relu (lin (braidRoot (left p) (right p)) x))=
      argument s (fun p => x (left p)-x (right p))
        (coefficient net.A (net.W k)) (lin (correctedHead net k) x) := by
  rw [lin_stateHead]
  simp only [lin_root,argument]
  rw [add_assoc,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simpa only [stateWeight,ite_mul,zero_mul] using
    state_value_split (s p) (coefficient net.A (net.W k) p) (x (left p)-x (right p))

theorem initial_argument (net : NormalizedNetwork N h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hcard : ∀ j,(rowSupport (net.A j)).card≤2) (k : Fin h₂) (x : Point N) :
    argument (initialState net k) (fun p => x (left p)-x (right p))
      (coefficient net.A (net.W k)) (lin (correctedHead net k) x)=net.inner k x := by
  calc
    _=lin (correctedHead net k) x+
        ∑ p : Pair N,coefficient net.A (net.W k) p*relu (x (left p)-x (right p)) := by
      unfold argument
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : coefficient net.A (net.W k) p=0 <;>
        simp [initialState,hp,value,MaxCaterpillar.relu,max_comm]
    _=net.inner k x :=
      (linear_combination_canonical (net.U k) net.A (net.W k) hnorm.1 hcard x).symm

theorem root_sum (p : Pair N) : ∑ i,braidRoot (left p) (right p) i=0 := by
  have hh := lin_root p (diag 1)
  simpa only [lin_diag,one_mul,diag,sub_self] using hh

theorem root_support (p : Pair N) : rowSupport (braidRoot (left p) (right p))={left p,right p} := by
  ext i
  by_cases hi : i=left p
  · subst i
    simp [mem_rowSupport,braidRoot,unitVec,pair_distinct p]
  · by_cases hj : i=right p
    · subst i
      simp [mem_rowSupport,braidRoot,unitVec,Ne.symm (pair_distinct p)]
    · simp [mem_rowSupport,braidRoot,unitVec,hi,hj]

theorem stateHead_sum (net : NormalizedNetwork N h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hcard : ∀ j,(rowSupport (net.A j)).card≤2) (k : Fin h₂) (s : Pair N→State) :
    ∑ i,stateHead net k s i=0 := by
  have hh := lin_stateHead net k s (diag 1)
  simp only [lin_diag,one_mul,diag,sub_self,mul_zero,ite_self,
    Finset.sum_const_zero,add_zero] at hh
  rw [hh,correctedHead,head_sum _ _ _ hnorm.1 hcard,hnorm.2.1 k]

/-- An exact decomposition of each ORIGINAL actual second neuron; one
finite real coefficient function works at all real inputs simultaneously.
There is no standalone forest or cover assumption on the original neuron. -/
theorem actual_neuron_forest_expansion (net : NormalizedNetwork N h₁ h₂)
    (hnorm : net.TranslationNormalized)
    (hcard : ∀ j,(rowSupport (net.A j)).card≤2) (k : Fin h₂) :
    ∃ d : UnitState net k→ℝ,∀ x : Point N,
      relu (net.inner k x)=∑ t,d t*relu (lin (stateHead net k t.val) x+
        ∑ p : Pair N,stateWeight net k t.val p*relu (lin (braidRoot (left p) (right p)) x)) := by
  obtain ⟨d,hd⟩ := forest_expansion (activeEdges net.A (net.W k)) left right
    (coefficient net.A (net.W k)) (lin (correctedHead net k)) relu
    (initialState net k) (by rw [active_initialState])
  refine ⟨d,fun x => ?_⟩
  have hh := hd x
  change relu (argument (initialState net k) _ _ _)=
    ∑ t,d t*relu (argument t.val _ _ _) at hh
  rw [initial_argument net hnorm hcard k x] at hh
  simpa only [←state_argument_realization] using hh

#check @actual_neuron_forest_expansion
#print axioms state_argument_realization
#print axioms initial_argument
#print axioms stateHead_sum
#print axioms actual_neuron_forest_expansion
end MaxCaterpillar.ExponentialPush.DictionaryBridge
