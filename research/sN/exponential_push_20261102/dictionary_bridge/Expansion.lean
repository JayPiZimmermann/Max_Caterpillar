import research.sN.exponential_push_20261102.dictionary_bridge.ThreeState
import research.sN.exponential_push_20261102.forest_matching.Cycle
import Mathlib.LinearAlgebra.Finsupp

/-! Exact all-real forest expansion by finite original edge states.
The theorem constructs the decomposition by decreasing the active edge
count, rather than imposing a forest representation as a hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DictionaryBridge
open BigOperators ForestMatching
attribute [local instance] Classical.propDecidable
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

lemma active_card_decreases (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (T : Finset ι) (hS : S⊆active s) (hT : T⊂S) :
    (active (updateState s S reverse T)).card<(active s).card := by
  rw [active_updateState]
  have hrem : (S\T).Nonempty := Finset.sdiff_nonempty.mpr (not_le_of_gt hT)
  exact Finset.card_lt_card (Finset.sdiff_ssubset
    ((Finset.sdiff_subset S T).trans hS) hrem)

def stateUnit (s : ι→State) (a b : ι→V) (c : ι→ℝ)
    (h : (V→ℝ)→ℝ) (F : ℝ→ℝ) : (V→ℝ)→ℝ :=
  fun x => F (argument s (fun i => x (a i)-x (b i)) c (h x))

/-- All nonlinear edges stay among the original active edges. The heads
are still formed solely by original linearized edge states. -/
def ForestState (A : Finset ι) (a b : ι→V) :=
  {s : ι→State // active s⊆A ∧ (indexedGraph (active s) a b).IsAcyclic}

instance forestStateFintype (A : Finset ι) (a b : ι→V) : Fintype (ForestState A a b) := by
  classical
  unfold ForestState
  infer_instance

def forestSpan (A : Finset ι) (a b : ι→V) (c : ι→ℝ)
    (h : (V→ℝ)→ℝ) (F : ℝ→ℝ) : Submodule ℝ ((V→ℝ)→ℝ) :=
  Submodule.span ℝ (Set.range fun t : ForestState A a b => stateUnit t.val a b c h F)

/-- Every original state unit is in the span of states with a genuine
forest nonlinear graph and no nonlinear edge outside the original graph.
The outer scalar function and signed real weights are arbitrary. -/
theorem stateUnit_mem_forestSpan (A : Finset ι) (a b : ι→V) (c : ι→ℝ)
    (h : (V→ℝ)→ℝ) (F : ℝ→ℝ) (s : ι→State) (hsub : active s⊆A) :
    stateUnit s a b c h F∈forestSpan A a b c h F := by
  suffices main : ∀ m : ℕ,∀ t : ι→State,(active t).card=m → active t⊆A →
      stateUnit t a b c h F∈forestSpan A a b c h F from
    main _ s rfl hsub
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro t hcard htA
    by_cases hg : (indexedGraph (active t) a b).IsAcyclic
    · exact Submodule.subset_span ⟨⟨t,htA,hg⟩,rfl⟩
    · obtain ⟨S,hS,hSn,reverse,hzero⟩ := indexedGraph_oriented_cycle (active t) a b hg
      have hactive : ∀ i∈S,t i=2 := fun i hi => (Finset.mem_filter.mp (hS hi)).2
      have heq : stateUnit t a b c h F=
          -∑ T in S.powerset.erase S,(-1:ℝ)^(S\T).card •
            stateUnit (updateState t S reverse T) a b c h F := by
        funext x
        simp only [Pi.neg_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
        exact three_state_circuit_deletion t S reverse
          (fun i => x (a i)-x (b i)) c (h x) F hSn hactive (hzero x)
      rw [heq]
      apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro T hT
      have hTS : T⊂S := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2,(Finset.mem_erase.mp hT).1⟩
      apply Submodule.smul_mem
      apply ih _ ((active_card_decreases t S reverse T hS hTS).trans_eq hcard)
        (updateState t S reverse T) rfl
      exact (active_updateState_subset t S reverse T).trans htA

/-- A finite all-input identity, not merely an abstract span statement.
The same real coefficient function works on every chamber and boundary. -/
theorem forest_expansion (A : Finset ι) (a b : ι→V) (c : ι→ℝ)
    (h : (V→ℝ)→ℝ) (F : ℝ→ℝ) (s : ι→State) (hsub : active s⊆A) :
    ∃ d : ForestState A a b→ℝ,∀ x : V→ℝ,
      stateUnit s a b c h F x=∑ t,d t*stateUnit t.val a b c h F x := by
  have hm := stateUnit_mem_forestSpan A a b c h F s hsub
  obtain ⟨d,hd⟩ :=
    (mem_span_range_iff_exists_fun (R:=ℝ)
      (v:=fun t : ForestState A a b => stateUnit t.val a b c h F)).mp hm
  refine ⟨d,fun x => ?_⟩
  have hh := congrFun hd x
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hh.symm

/-- Coalescing identical original states bounds the required expansion by
3^E, where E is the ORIGINAL indexed edge count. No width preservation is
claimed, and no coefficient-norm bound is inferred from this count. -/
theorem forest_states_card_le (A : Finset ι) (a b : ι→V) :
    Fintype.card (ForestState A a b)≤3^Fintype.card ι := by
  calc Fintype.card (ForestState A a b)≤Fintype.card (ι→State) :=
         Fintype.card_le_of_injective (fun t : ForestState A a b => t.val)
           (fun _ _ ht => Subtype.ext ht)
       _=3^Fintype.card ι := state_space_card

#check @forest_expansion
#print axioms active_card_decreases
#print axioms stateUnit_mem_forestSpan
#print axioms forest_expansion
#print axioms forest_states_card_le
end MaxCaterpillar.ExponentialPush.DictionaryBridge
