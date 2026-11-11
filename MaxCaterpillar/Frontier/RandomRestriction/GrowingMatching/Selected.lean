import MaxCaterpillar.Frontier.RandomRestriction.SelectedSetProbability
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.TwoEdges.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-! Actual selected disjoint-edge matchings. Edges are ordinary unordered
Sym2 edges, selected labels are sent to the first k positions by a genuine
uniform permutation. The bound retains the factorial improvement. -/
set_option autoImplicit false
open scoped BigOperators
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
variable {n k d q : ℕ}

noncomputable def selectedTuples (n k d : ℕ) : Finset (Fin d ↪ Fin n) := by
  classical
  exact Finset.univ.filter fun a => ∀ i, (a i).val < k

@[simp] theorem mem_selectedTuples (a : Fin d ↪ Fin n) :
    a ∈ selectedTuples n k d ↔ ∀ i, (a i).val < k := by
  classical
  simp [selectedTuples]

def prefixEmbedding (hkn : k ≤ n) : Fin k ↪ Fin n where
  toFun i := ⟨i.val,lt_of_lt_of_le i.isLt hkn⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun z : Fin n => z.val) he)

def selectedTupleEquiv (hkn : k ≤ n) :
    (Fin d ↪ Fin k) ≃ {a : Fin d ↪ Fin n // a ∈ selectedTuples n k d} where
  toFun a := ⟨a.trans (prefixEmbedding hkn),by
    apply (mem_selectedTuples _).mpr
    intro i
    exact (a i).isLt⟩
  invFun a :=
    { toFun := fun i => ⟨(a.val i).val,((mem_selectedTuples a.val).mp a.property) i⟩
      inj' := by
        intro i j he
        exact a.val.injective (Fin.ext (congrArg (fun z : Fin k => z.val) he)) }
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

theorem selectedTuples_card (hkn : k ≤ n) :
    (selectedTuples n k d).card = k.descFactorial d := by
  have hh := Fintype.card_congr (selectedTupleEquiv (d:=d) hkn)
  rw [Fintype.card_coe,UniformTuples.card_tuples] at hh
  exact hh.symm

/-- Exact law for actual sets of labels, with empty/oversized cases included. -/
theorem containment_card_mul_descFactorial (hkn : k ≤ n) (T : Finset (Fin n)) :
    (GoodEvent.containmentEvent k T).card * n.descFactorial T.card =
      k.descFactorial T.card * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let e := SelectedSetProbability.setEmbedding T
  have he : GoodEvent.containmentEvent k T =
      UniformTuples.event e (selectedTuples n k T.card) := by
    ext σ
    rw [GoodEvent.mem_containmentEvent,UniformTuples.mem_event,mem_selectedTuples]
    constructor
    · intro h i
      exact (GoodEvent.mem_smallRankGaps σ _).mp
        (h (SelectedSetProbability.setEmbedding_mem T i))
    · intro h v hv
      obtain ⟨i,hi⟩ := SelectedSetProbability.setEmbedding_surjective T v hv
      rw [GoodEvent.mem_smallRankGaps,←hi]
      exact h i
  rw [he]
  have hh := UniformTuples.card_event_mul_tuple_card e (selectedTuples n k T.card)
  rw [UniformTuples.card_tuples,selectedTuples_card hkn] at hh
  exact hh

/-- Actual q-element sets of ordinary pairwise vertex-disjoint graph edges. -/
noncomputable def matchings (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : ℕ) : Finset (Finset (Sym2 (Fin n))) := by
  classical
  exact (G.edgeFinset.powersetCard q).filter fun B =>
    ∀ e ∈ B, ∀ f ∈ B, e ≠ f →
      Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f)

@[simp] theorem mem_matchings (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : Finset (Sym2 (Fin n))) :
    B ∈ matchings G q ↔ B ⊆ G.edgeFinset ∧ B.card = q ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f →
        Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f) := by
  classical
  simp only [matchings,Finset.mem_filter,Finset.mem_powersetCard]
  tauto

noncomputable def matchingVertices (B : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  GraphRestriction.pairVertices B

theorem matchingVertices_card (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : Finset (Sym2 (Fin n))) (hB : B ∈ matchings G q) :
    (matchingVertices B).card = 2*q := by
  classical
  obtain ⟨hsub,hcard,hd⟩ := (mem_matchings G B).mp hB
  unfold matchingVertices GraphRestriction.pairVertices
  rw [Finset.card_biUnion]
  · calc
      (∑ e in B, (GraphRestriction.edgeVertices e).card) = ∑ _e in B, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        exact GraphRestriction.edgeVertices_card G e (hsub he)
      _ = 2*q := by simp [hcard,Nat.mul_comm]
  · intro e he f hf hef
    exact hd e he f hf hef

theorem matchings_card_le_choose (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (matchings G q).card ≤ G.edgeFinset.card.choose q := by
  classical
  calc
    (matchings G q).card ≤ (G.edgeFinset.powersetCard q).card :=
      Finset.card_le_of_subset (Finset.filter_subset _ _)
    _ = _ := Finset.card_powersetCard q G.edgeFinset

/-- Literal existence, with no distribution or probability premise. -/
def hasSelectedMatching (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k q : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ B ∈ matchings G q, matchingVertices B ⊆ GoodEvent.smallRankGaps σ k

noncomputable def selectedEvent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k q : ℕ) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (hasSelectedMatching G k q)

@[simp] theorem mem_selectedEvent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ selectedEvent G k q ↔ hasSelectedMatching G k q σ := by
  classical
  simp [selectedEvent]

theorem selectedEvent_subset_union (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    selectedEvent G k q ⊆ (matchings G q).biUnion fun B =>
      GoodEvent.containmentEvent k (matchingVertices B) := by
  classical
  intro σ hσ
  obtain ⟨B,hB,hs⟩ := (mem_selectedEvent G σ).mp hσ
  exact Finset.mem_biUnion.mpr ⟨B,hB,(GoodEvent.mem_containmentEvent _ σ).mpr hs⟩

/-- Stronger union bound retains the actual number of q-matchings. -/
theorem selectedEvent_card_mul_le_matchings (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hkn : k ≤ n) :
    (selectedEvent G k q).card * n.descFactorial (2*q) ≤
      (matchings G q).card *
        (k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n))) := by
  classical
  have hc : (selectedEvent G k q).card ≤
      ∑ B in matchings G q, (GoodEvent.containmentEvent k (matchingVertices B)).card :=
    (Finset.card_le_of_subset (selectedEvent_subset_union G)).trans Finset.card_biUnion_le
  calc
    (selectedEvent G k q).card * n.descFactorial (2*q) ≤
        (∑ B in matchings G q,
          (GoodEvent.containmentEvent k (matchingVertices B)).card) *
            n.descFactorial (2*q) := Nat.mul_le_mul_right _ hc
    _ = ∑ B in matchings G q,
        (GoodEvent.containmentEvent k (matchingVertices B)).card *
          n.descFactorial (2*q) := Finset.sum_mul
    _ = ∑ _B in matchings G q,
        k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n)) := by
      apply Finset.sum_congr rfl
      intro B hB
      have hh := containment_card_mul_descFactorial hkn (matchingVertices B)
      rw [matchingVertices_card G B hB] at hh
      exact hh
    _ = _ := by simp

/-- Binomial union bound before division; no positivity premise. -/
theorem selectedEvent_card_mul_le_choose (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hkn : k ≤ n) :
    (selectedEvent G k q).card * n.descFactorial (2*q) ≤
      G.edgeFinset.card.choose q *
        (k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n))) :=
  (selectedEvent_card_mul_le_matchings G hkn).trans
    (Nat.mul_le_mul_right _ (matchings_card_le_choose G))

/-- Factorial retained without natural division. -/
theorem selectedEvent_card_mul_factorial_le (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hkn : k ≤ n) :
    q.factorial * ((selectedEvent G k q).card * n.descFactorial (2*q)) ≤
      G.edgeFinset.card^q *
        (k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n))) := by
  have hh := Nat.mul_le_mul_left q.factorial (selectedEvent_card_mul_le_choose (q:=q) G hkn)
  calc
    _ ≤ q.factorial * (G.edgeFinset.card.choose q *
        (k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n)))) := hh
    _ = G.edgeFinset.card.descFactorial q *
        (k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n))) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose G.edgeFinset.card q]
      ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow _ _)

/-- Oversized requests are empty before division is taken. -/
theorem selectedEvent_empty_of_prefix_lt (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hkn : k ≤ n) (hkq : k < 2*q) :
    selectedEvent G k q = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro σ hσ
  obtain ⟨B,hB,hs⟩ := (mem_selectedEvent G σ).mp hσ
  have hc := Finset.card_le_of_subset hs
  rw [matchingVertices_card G B hB,GoodEvent.card_smallRankGaps hkn σ] at hc
  exact (not_le_of_gt hkq) hc

/-- Actual uniform-permutation probability, with binomial edge count. -/
theorem selectedEvent_fraction_le_choose (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hkn : k ≤ n) :
    ((selectedEvent G k q).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤
      (G.edgeFinset.card.choose q : ℝ) * (k.descFactorial (2*q) : ℝ) /
        (n.descFactorial (2*q) : ℝ) := by
  by_cases hqn : 2*q ≤ n
  · have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩)
    have hd : (0 : ℝ) < n.descFactorial (2*q) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h =>
        (not_lt_of_ge hqn) (Nat.descFactorial_eq_zero_iff_lt.mp h))
    apply (div_le_div_iff hp hd).mpr
    have hh := selectedEvent_card_mul_le_choose (q:=q) G hkn
    exact_mod_cast (by simpa only [mul_assoc] using hh)
  · have hlt : n < 2*q := Nat.lt_of_not_ge hqn
    rw [selectedEvent_empty_of_prefix_lt G hkn (lt_of_le_of_lt hkn hlt)]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

/-- Requested factorial-strengthened probability bound for every q,
including q=0 and oversized q. -/
theorem selectedEvent_fraction_le (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hkn : k ≤ n) :
    ((selectedEvent G k q).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤
      ((G.edgeFinset.card : ℝ)^q / (q.factorial : ℝ)) *
        ((k.descFactorial (2*q) : ℝ) / (n.descFactorial (2*q) : ℝ)) := by
  have hc : (G.edgeFinset.card.choose q : ℝ) ≤
      (G.edgeFinset.card : ℝ)^q / (q.factorial : ℝ) :=
    Nat.choose_le_pow q G.edgeFinset.card
  have hn : (0 : ℝ) ≤ (k.descFactorial (2*q) : ℝ) /
      (n.descFactorial (2*q) : ℝ) := by positivity
  calc
    _ ≤ (G.edgeFinset.card.choose q : ℝ) * (k.descFactorial (2*q) : ℝ) /
        (n.descFactorial (2*q) : ℝ) := selectedEvent_fraction_le_choose G hkn
    _ = (G.edgeFinset.card.choose q : ℝ) *
        ((k.descFactorial (2*q) : ℝ) / (n.descFactorial (2*q) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hn

/-- Empty matching boundary control. -/
theorem selectedEvent_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    selectedEvent G k 0 = Finset.univ := by
  classical
  ext σ
  simp only [mem_selectedEvent,Finset.mem_univ,iff_true]
  refine ⟨∅,?_,?_⟩
  · simp [mem_matchings]
  · simp [matchingVertices,GraphRestriction.pairVertices]

#check @selectedEvent_card_mul_le_choose
#check @selectedEvent_card_mul_factorial_le
#check @selectedEvent_fraction_le
#print axioms containment_card_mul_descFactorial
#print axioms matchingVertices_card
#print axioms selectedEvent_card_mul_factorial_le
#print axioms selectedEvent_fraction_le
#print axioms selectedEvent_zero
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
