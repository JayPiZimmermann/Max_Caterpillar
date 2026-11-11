import research.sN.exponential_push_20261102.structural.CircuitDeletion

/-! Original-orientation circuit deletion with exactly three edge states.
Research only: omitted0, linear1 and nonlinear2. No new edge, coefficient,
or independent head parameter is introduced by the deletion identity.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DictionaryBridge
open BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev State := Fin 3

@[simp] lemma state_two_ne_zero : (2:State)≠0 := by decide
@[simp] lemma state_two_ne_one : (2:State)≠1 := by decide
@[simp] lemma state_zero_ne_two : (0:State)≠2 := by decide
@[simp] lemma state_one_ne_two : (1:State)≠2 := by decide

def value (s : State) (z : ℝ) : ℝ :=
  if s=0 then 0 else if s=1 then z else max z 0

def oriented (reverse : Bool) (z : ℝ) : ℝ := if reverse then -z else z

def argument (s : ι→State) (ell c : ι→ℝ) (a : ℝ) : ℝ :=
  a+∑ i,c i*value (s i) (ell i)

def updateState (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (T : Finset ι) (i : ι) : State :=
  if i∈S ∧ i∉T then (if reverse i then 1 else 0) else s i

def reorientedBase (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (ell c : ι→ℝ) (a : ℝ) : ℝ :=
  a+∑ i,if i∈S then (if reverse i then c i*ell i else 0)
    else c i*value (s i) (ell i)

lemma max_reversal (z : ℝ) : max z 0=z+max (-z) 0 := by
  rcases le_total 0 z with h|h
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]
    ring

lemma sum_subset_as_univ (T : Finset ι) (f : ι→ℝ) :
    (∑ i in T,f i)=∑ i,if i∈T then f i else 0 := by
  calc
    (∑ i in T,f i)=∑ i in T,if i∈T then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos hi]
    _=∑ i,if i∈T then f i else 0 :=
      Finset.sum_subset (Finset.subset_univ T) (by intro i _ hi;rw [if_neg hi])

lemma state_term_reorientation (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (T : Finset ι) (hTS : T⊆S) (ell c : ι→ℝ)
    (hactive : ∀ i∈S,s i=2) (i : ι) :
    c i*value (updateState s S reverse T i) (ell i)=
      (if i∈S then (if reverse i then c i*ell i else 0)
        else c i*value (s i) (ell i))+
      (if i∈T then c i*max (oriented (reverse i) (ell i)) 0 else 0) := by
  by_cases hiS : i∈S
  · have hs := hactive i hiS
    by_cases hiT : i∈T
    · cases hr : reverse i
      · simp [updateState,value,oriented,hiS,hiT,hs,hr]
      · simp only [updateState,hiS,hiT,hs,hr,oriented,value,
          not_true_eq_false,and_false,if_false,if_true,state_two_ne_zero,state_two_ne_one]
        rw [max_reversal (ell i)]
        ring
    · cases hr : reverse i <;> norm_num [updateState,value,oriented,hiS,hiT,hr,State]
  · have hiT : i∉T := fun h => hiS (hTS h)
    simp [updateState,hiS,hiT]

/-- Reversing a retained comparison cancels its head correction. Deleting
it yields its ORIGINAL linear state or omitted state, never a new form. -/
theorem argument_reorientation (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (T : Finset ι) (hTS : T⊆S) (ell c : ι→ℝ) (a : ℝ)
    (hactive : ∀ i∈S,s i=2) :
    argument (updateState s S reverse T) ell c a=
      reorientedBase s S reverse ell c a+∑ i in T,c i*max (oriented (reverse i) (ell i)) 0 := by
  unfold argument reorientedBase
  rw [sum_subset_as_univ T (fun i => c i*max (oriented (reverse i) (ell i)) 0),
    add_assoc,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact state_term_reorientation s S reverse T hTS ell c hactive i

@[simp] lemma updateState_self (s : ι→State) (S : Finset ι) (reverse : ι→Bool) :
    updateState s S reverse S=s := by
  funext i
  simp [updateState]

/-- Exact original-three-state circuit deletion, for every real evaluation
and arbitrary signed coefficients and scalar outer function. -/
theorem three_state_circuit_deletion (s : ι→State) (S : Finset ι)
    (reverse : ι→Bool) (ell c : ι→ℝ) (a : ℝ) (F : ℝ→ℝ)
    (hS : S.Nonempty) (hactive : ∀ i∈S,s i=2)
    (hzero : ∑ i in S,oriented (reverse i) (ell i)=0) :
    F (argument s ell c a)=
      -∑ T in S.powerset.erase S,(-1:ℝ)^(S\T).card*
        F (argument (updateState s S reverse T) ell c a) := by
  have harg := argument_reorientation s S reverse S (Finset.Subset.refl S) ell c a hactive
  rw [updateState_self] at harg
  have hc := circuit_deletion S (fun i => oriented (reverse i) (ell i)) c
    (reorientedBase s S reverse ell c a) F hS hzero
  rw [←harg] at hc
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hTS : T⊆S := Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2
  rw [argument_reorientation s S reverse T hTS ell c a hactive]

def active (s : ι→State) : Finset ι := Finset.univ.filter fun i => s i=2

/-- The new nonlinear edges are exactly the old nonlinear edges after the
deleted cycle edges are removed. This preserves every matching bound. -/
theorem active_updateState (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (T : Finset ι) :
    active (updateState s S reverse T)=active s\(S\T) := by
  ext i
  by_cases hiS : i∈S <;> by_cases hiT : i∈T <;> cases hr : reverse i <;>
    simp [active,updateState,hiS,hiT,hr]

theorem active_updateState_subset (s : ι→State) (S : Finset ι) (reverse : ι→Bool)
    (T : Finset ι) : active (updateState s S reverse T)⊆active s := by
  rw [active_updateState]
  exact Finset.sdiff_subset _ _

/-- There are only3^E original-orientation face states. Consequently any
forest expansion in these states can be coalesced to at most3^E terms. -/
theorem state_space_card : Fintype.card (ι→State)=3^Fintype.card ι := by
  simp only [Fintype.card_fun,Fintype.card_fin]

theorem distinct_states_card_le (K : Finset (ι→State)) : K.card≤3^Fintype.card ι := by
  calc K.card≤Fintype.card (ι→State) := Finset.card_le_univ K
       _=3^Fintype.card ι := state_space_card

#check @three_state_circuit_deletion
#print axioms argument_reorientation
#print axioms three_state_circuit_deletion
#print axioms active_updateState
#print axioms distinct_states_card_le
end MaxCaterpillar.ExponentialPush.DictionaryBridge
