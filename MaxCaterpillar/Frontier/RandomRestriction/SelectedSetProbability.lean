import MaxCaterpillar.Frontier.RandomRestriction.UniformTuples
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset

/-!
# Exact containment probabilities for the five selected labels

A full permutation sends LABELS to POSITIONS. Its selected set is the literal
preimage of positions 0,...,4. UniformTuples proves the actual permutation law;
no uniform-subset hypothesis is required. The tuple count works also for d=0
and d>5, where the selected tuple space is empty in the latter case.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.SelectedSetProbability

variable {N d : ℕ}

noncomputable def selectedLabels (σ : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  GoodEvent.smallRankGaps σ 5

@[simp] theorem mem_selectedLabels (σ : Equiv.Perm (Fin N)) (v : Fin N) :
    v ∈ selectedLabels σ ↔ (σ v).val<5 := GoodEvent.mem_smallRankGaps σ v

theorem selectedLabels_card (hN : 5≤N) (σ : Equiv.Perm (Fin N)) :
    (selectedLabels σ).card=5 := GoodEvent.card_smallRankGaps hN σ

noncomputable def selectedTuples (N d : ℕ) : Finset (Fin d ↪ Fin N) := by
  classical
  exact Finset.univ.filter fun a => ∀ i, (a i).val<5

@[simp] theorem mem_selectedTuples (a : Fin d ↪ Fin N) :
    a ∈ selectedTuples N d ↔ ∀ i, (a i).val<5 := by
  classical
  simp [selectedTuples]

def prefixFiveEmbedding (hN : 5≤N) : Fin 5 ↪ Fin N where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt hN⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun z : Fin N => z.val) he)

/-- Actual codomain restriction, including empty tuple spaces. -/
def selectedTupleEquiv (hN : 5≤N) :
    (Fin d ↪ Fin 5) ≃ {a : Fin d ↪ Fin N // a ∈ selectedTuples N d} where
  toFun a := ⟨a.trans (prefixFiveEmbedding hN),by
    apply (mem_selectedTuples _).mpr
    intro i
    exact (a i).isLt⟩
  invFun a :=
    { toFun := fun i => ⟨(a.val i).val,((mem_selectedTuples a.val).mp a.property) i⟩
      inj' := by
        intro i j he
        exact a.val.injective (Fin.ext (congrArg (fun z : Fin 5 => z.val) he)) }
  left_inv a := by
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    apply Fin.ext
    rfl

theorem selectedTuples_card (hN : 5≤N) :
    (selectedTuples N d).card=Nat.descFactorial 5 d := by
  have hh := Fintype.card_congr (selectedTupleEquiv (d:=d) hN)
  rw [Fintype.card_coe,UniformTuples.card_tuples] at hh
  exact hh.symm

/-- Literal all-permutation event for a fixed injection of distinct labels. -/
noncomputable def tupleEvent (e : Fin d ↪ Fin N) : Finset (Equiv.Perm (Fin N)) := by
  classical
  exact Finset.univ.filter fun σ => ∀ i, (σ (e i)).val<5

@[simp] theorem mem_tupleEvent (e : Fin d ↪ Fin N) (σ : Equiv.Perm (Fin N)) :
    σ ∈ tupleEvent e ↔ ∀ i, (σ (e i)).val<5 := by
  classical
  simp [tupleEvent]

theorem tupleEvent_eq_uniformTuples (e : Fin d ↪ Fin N) :
    tupleEvent e=UniformTuples.event e (selectedTuples N d) := by
  ext σ
  simp only [mem_tupleEvent,UniformTuples.mem_event,
    mem_selectedTuples,UniformTuples.induced_apply]

/-- Exact natural count, with no probability or positivity premise. -/
theorem tupleEvent_card_mul (hN : 5≤N) (e : Fin d ↪ Fin N) :
    (tupleEvent e).card*N.descFactorial d=
      Nat.descFactorial 5 d*Fintype.card (Equiv.Perm (Fin N)) := by
  rw [tupleEvent_eq_uniformTuples]
  have hh := UniformTuples.card_event_mul_tuple_card e (selectedTuples N d)
  rw [UniformTuples.card_tuples,selectedTuples_card hN] at hh
  exact hh

theorem tupleEvent_fraction (hN : 5≤N) (e : Fin d ↪ Fin N) :
    ((tupleEvent e).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ)=
      (Nat.descFactorial 5 d : ℝ)/(N.descFactorial d : ℝ) := by
  rw [tupleEvent_eq_uniformTuples]
  have hh := UniformTuples.real_fraction_eq e (selectedTuples N d)
  rw [selectedTuples_card hN] at hh
  exact hh

/-- The actual literal event that all vertices of a fixed set are selected. -/
noncomputable def containsEvent (T : Finset (Fin N)) : Finset (Equiv.Perm (Fin N)) :=
  GoodEvent.containmentEvent 5 T

@[simp] theorem mem_containsEvent (T : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) :
    σ ∈ containsEvent T ↔ T ⊆ selectedLabels σ := GoodEvent.mem_containmentEvent T σ

/-- Enumerate a genuine finite set once, with no repetitions. -/
noncomputable def setEmbedding (T : Finset (Fin N)) : Fin T.card ↪ Fin N :=
  T.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype fun v => v ∈ T)

theorem setEmbedding_mem (T : Finset (Fin N)) (i : Fin T.card) :
    setEmbedding T i ∈ T := (T.equivFin.symm i).property

theorem setEmbedding_surjective (T : Finset (Fin N)) (v : Fin N) (hv : v∈T) :
    ∃ i, setEmbedding T i=v := by
  refine ⟨T.equivFin ⟨v,hv⟩,?_⟩
  change (T.equivFin.symm (T.equivFin ⟨v,hv⟩)).val=v
  rw [Equiv.symm_apply_apply]

theorem containsEvent_eq_tupleEvent (T : Finset (Fin N)) :
    containsEvent T=tupleEvent (setEmbedding T) := by
  ext σ
  rw [mem_containsEvent,mem_tupleEvent]
  constructor
  · intro h i
    exact (mem_selectedLabels σ _).mp (h (setEmbedding_mem T i))
  · intro h v hv
    obtain ⟨i,hi⟩ := setEmbedding_surjective T v hv
    rw [mem_selectedLabels,←hi]
    exact h i

/-- The requested exact set law, valid for every finite set, even if its
cardinality exceeds five (both favorable-event counts then vanish). -/
theorem containsEvent_card_mul_descFactorial (hN : 5≤N) (T : Finset (Fin N)) :
    (containsEvent T).card*N.descFactorial T.card=
      Nat.descFactorial 5 T.card*Fintype.card (Equiv.Perm (Fin N)) := by
  rw [containsEvent_eq_tupleEvent]
  exact tupleEvent_card_mul hN _

theorem containsEvent_fraction (hN : 5≤N) (T : Finset (Fin N)) :
    ((containsEvent T).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ)=
      (Nat.descFactorial 5 T.card : ℝ)/(N.descFactorial T.card : ℝ) := by
  rw [containsEvent_eq_tupleEvent]
  exact tupleEvent_fraction hN _

/-- The denominator is positive because T really is a set of distinct labels. -/
theorem denominator_pos (T : Finset (Fin N)) : 0<N.descFactorial T.card :=
  UniformTuples.tuple_count_pos (setEmbedding T)

theorem containsEvent_empty_of_card_gt_five (hN : 5≤N)
    (T : Finset (Fin N)) (hT : 5<T.card) : containsEvent T=∅ :=
  GoodEvent.containment_event_empty_of_card_gt hN T hT

/-- Requesting more labels makes an event smaller. -/
theorem containsEvent_antitone {I T : Finset (Fin N)} (hIT : I⊆T) :
    containsEvent T⊆containsEvent I := by
  intro σ hσ
  exact (mem_containsEvent I σ).mpr (hIT.trans ((mem_containsEvent T σ).mp hσ))

/-- Any support of size at least three contains an actual three-element
subset. No maximum support size is assumed. -/
theorem support_containsEvent_card_mul_le (hN : 5≤N)
    (T : Finset (Fin N)) (hT : 3≤T.card) :
    (containsEvent T).card*N.descFactorial 3≤
      60*Fintype.card (Equiv.Perm (Fin N)) := by
  classical
  obtain ⟨I,hI⟩ := Finset.powersetCard_nonempty hT
  obtain ⟨hIT,hcard⟩ := Finset.mem_powersetCard.mp hI
  have hcount := Nat.mul_le_mul_right (N.descFactorial 3)
    (Finset.card_le_of_subset (containsEvent_antitone hIT))
  have hexact := containsEvent_card_mul_descFactorial hN I
  rw [hcard,show Nat.descFactorial 5 3=60 by decide] at hexact
  exact hcount.trans hexact.le

theorem support_containsEvent_fraction_le (hN : 5≤N)
    (T : Finset (Fin N)) (hT : 3≤T.card) :
    ((containsEvent T).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ)≤
      60/(N.descFactorial 3 : ℝ) := by
  have hP : (0 : ℝ)<Fintype.card (Equiv.Perm (Fin N)) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin N)⟩)
  have hD : (0 : ℝ)<N.descFactorial 3 := by
    have h : 3≤N := by linarith only [hN]
    have hp : 0<N.descFactorial 3 := Nat.pos_of_ne_zero (by
      intro hz
      have hlt := Nat.descFactorial_eq_zero_iff_lt.mp hz
      exact (not_lt_of_ge h) hlt)
    exact_mod_cast hp
  apply (div_le_div_iff hP hD).mpr
  exact_mod_cast support_containsEvent_card_mul_le hN T hT

theorem fourSet_containsEvent_card_mul (hN : 5≤N)
    (T : Finset (Fin N)) (hT : T.card=4) :
    (containsEvent T).card*N.descFactorial 4=
      120*Fintype.card (Equiv.Perm (Fin N)) := by
  have hh := containsEvent_card_mul_descFactorial hN T
  rw [hT,show Nat.descFactorial 5 4=120 by decide] at hh
  exact hh

theorem fourSet_containsEvent_fraction (hN : 5≤N)
    (T : Finset (Fin N)) (hT : T.card=4) :
    ((containsEvent T).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ)=
      120/(N.descFactorial 4 : ℝ) := by
  rw [containsEvent_fraction hN T,hT]
  norm_num

#check @containsEvent_card_mul_descFactorial
#check @support_containsEvent_card_mul_le
#print axioms selectedLabels_card
#print axioms selectedTuples_card
#print axioms containsEvent_card_mul_descFactorial
#print axioms containsEvent_fraction
#print axioms support_containsEvent_card_mul_le
#print axioms support_containsEvent_fraction_le
#print axioms fourSet_containsEvent_fraction
end MaxCaterpillar.Frontier.RandomRestriction.SelectedSetProbability
