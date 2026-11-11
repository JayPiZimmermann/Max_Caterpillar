import Mathlib

/-!
# Cartesian trees are uniquely determined by their actual inorder words

The raw words consist of a nonempty leaf list and a distinct gap-rank list
with one fewer entry. A strict maximum-heap plane tree serializes to these
words bijectively. This is independent of an orientation distribution: raw
permutation configurations can be encoded by the words first.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.Cartesian

inductive PlaneTree (α β : Type*) where
  | leaf : α → PlaneTree α β
  | branch : β → PlaneTree α β → PlaneTree α β → PlaneTree α β

variable {α β : Type*}

def inorderLeaves : PlaneTree α β → List α
  | .leaf a => [a]
  | .branch _ l r => inorderLeaves l ++ inorderLeaves r

def inorderGaps : PlaneTree α β → List β
  | .leaf _ => []
  | .branch k l r => inorderGaps l ++ k :: inorderGaps r

theorem inorder_length (t : PlaneTree α β) :
    (inorderLeaves t).length = (inorderGaps t).length + 1 := by
  induction t with
  | leaf a => rfl
  | branch k l r ihl ihr =>
    simp only [inorderLeaves, inorderGaps, List.length_append, List.length_cons]
    linarith only [ihl, ihr]

variable [LinearOrder β]

def HeapOrdered : PlaneTree α β → Prop
  | .leaf _ => True
  | .branch k l r => HeapOrdered l ∧ HeapOrdered r ∧
      (∀ a ∈ inorderGaps l, a < k) ∧ (∀ a ∈ inorderGaps r, a < k)

lemma gap_le_root {k : β} {l r : PlaneTree α β}
    (h : HeapOrdered (.branch k l r)) (a : β)
    (ha : a ∈ inorderGaps (.branch k l r)) : a ≤ k := by
  rcases h with ⟨_, _, hl, hr⟩
  simp only [inorderGaps, List.mem_append, List.mem_cons] at ha
  rcases ha with ha | ha | ha
  · exact le_of_lt (hl a ha)
  · exact le_of_eq ha
  · exact le_of_lt (hr a ha)

lemma split_at_unique {δ : Type*} (a : δ) (l r l' r' : List δ)
    (ha : a ∉ l) (ha' : a ∉ l') (he : l ++ a :: r = l' ++ a :: r') :
    l = l' ∧ r = r' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => exact ⟨rfl, List.cons.inj he |>.2⟩
    | cons b bs =>
      have hab : a = b := List.cons.inj he |>.1
      exact False.elim (ha' (by simp only [List.mem_cons]; exact Or.inl hab))
  | cons b bs ih =>
    cases l' with
    | nil =>
      have hba : b = a := List.cons.inj he |>.1
      exact False.elim (ha (by simp only [List.mem_cons]; exact Or.inl hba.symm))
    | cons c cs =>
      have hbc : b = c := List.cons.inj he |>.1
      have htail : bs ++ a :: r = cs ++ a :: r' := List.cons.inj he |>.2
      have hbs : a ∉ bs := fun h => ha (List.mem_cons_of_mem _ h)
      have hcs : a ∉ cs := fun h => ha' (List.mem_cons_of_mem _ h)
      obtain ⟨hl, hr⟩ := ih cs hbs hcs htail
      exact ⟨by rw [hbc, hl], hr⟩

lemma split_append_of_length {δ : Type*} (l r l' r' : List δ)
    (he : l ++ r = l' ++ r') (hlen : l.length = l'.length) :
    l = l' ∧ r = r' := by
  have hl := congrArg (List.take l.length) he
  rw [List.take_left, hlen, List.take_left] at hl
  refine ⟨hl, ?_⟩
  rw [hl] at he
  exact List.append_left_cancel he

/-- Uniqueness uses the heap condition, not a chosen tree orientation model. -/
theorem heap_inorder_injective (t t' : PlaneTree α β)
    (ht : HeapOrdered t) (ht' : HeapOrdered t')
    (hleaves : inorderLeaves t = inorderLeaves t')
    (hgaps : inorderGaps t = inorderGaps t') : t = t' := by
  induction t generalizing t' with
  | leaf a =>
    cases t' with
    | leaf b =>
      have hab : a = b := List.cons.inj hleaves |>.1
      rw [hab]
    | branch k l r =>
      have hk : k ∈ inorderGaps (.branch k l r) := by simp [inorderGaps]
      rw [← hgaps] at hk
      exact False.elim (List.not_mem_nil _ hk)
  | branch k l r ihl ihr =>
    cases t' with
    | leaf a =>
      have hk : k ∈ inorderGaps (.branch k l r) := by simp [inorderGaps]
      rw [hgaps] at hk
      exact False.elim (List.not_mem_nil _ hk)
    | branch k' l' r' =>
      have hkk' : k ≤ k' := gap_le_root ht' k (by rw [← hgaps]; simp [inorderGaps])
      have hk'k : k' ≤ k := gap_le_root ht k' (by rw [hgaps]; simp [inorderGaps])
      have he : k = k' := le_antisymm hkk' hk'k
      subst k'
      rcases ht with ⟨htl, htr, hkl, _hkr⟩
      rcases ht' with ⟨htl', htr', hkl', _hkr'⟩
      have hnot : k ∉ inorderGaps l := fun h => (lt_irrefl k) (hkl k h)
      have hnot' : k ∉ inorderGaps l' := fun h => (lt_irrefl k) (hkl' k h)
      obtain ⟨hgl, hgr⟩ := split_at_unique k (inorderGaps l) (inorderGaps r)
        (inorderGaps l') (inorderGaps r') hnot hnot' hgaps
      have hlen : (inorderLeaves l).length = (inorderLeaves l').length := by
        rw [inorder_length, inorder_length, hgl]
      obtain ⟨hll, hlr⟩ := split_append_of_length (inorderLeaves l) (inorderLeaves r)
        (inorderLeaves l') (inorderLeaves r') hleaves hlen
      have hel := ihl l' htl htl' hll hgl
      have her := ihr r' htr htr' hlr hgr
      rw [hel, her]

/-- Existence is proved from raw words by splitting at their maximum gap. -/
theorem exists_heap_tree (xs : List α) (rs : List β)
    (hlen : xs.length = rs.length + 1) (hnd : rs.Nodup) :
    ∃ t : PlaneTree α β, HeapOrdered t ∧ inorderLeaves t = xs ∧ inorderGaps t = rs := by
  classical
  have go : ∀ n : ℕ, ∀ (xs : List α) (rs : List β), rs.length = n →
      xs.length = rs.length + 1 → rs.Nodup →
      ∃ t : PlaneTree α β, HeapOrdered t ∧ inorderLeaves t = xs ∧ inorderGaps t = rs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro xs rs hrs hlen hnd
      by_cases hempty : rs = []
      · have hx : xs.length = 1 := by simpa only [hempty, List.length_nil, zero_add] using hlen
        obtain ⟨a, rfl⟩ := List.length_eq_one.mp hx
        exact ⟨.leaf a, trivial, rfl, hempty.symm⟩
      · have hnonempty : rs.toFinset.Nonempty := by
          obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil rs hempty
          exact ⟨a, List.mem_toFinset.mpr ha⟩
        let k := rs.toFinset.max' hnonempty
        have hkmem : k ∈ rs := List.mem_toFinset.mp (Finset.max'_mem _ _)
        have hmax : ∀ a ∈ rs, a ≤ k := by
          intro a ha
          exact Finset.le_max' _ _ (List.mem_toFinset.mpr ha)
        obtain ⟨L, R, hsplit⟩ := List.mem_split hkmem
        have hnd' : (L ++ k :: R).Nodup := hsplit ▸ hnd
        have hparts := List.nodup_append.mp hnd'
        have hndL : L.Nodup := hparts.1
        have hndR : R.Nodup := (List.nodup_cons.mp hparts.2.1).2
        have hkR : k ∉ R := (List.nodup_cons.mp hparts.2.1).1
        have hkL : k ∉ L := by
          intro hk
          exact (List.disjoint_left.mp hparts.2.2) hk (by simp)
        have hLmax : ∀ a ∈ L, a < k := by
          intro a ha
          have hle := hmax a (by rw [hsplit]; exact List.mem_append_left _ ha)
          exact lt_of_le_of_ne hle (fun he => hkL (he ▸ ha))
        have hRmax : ∀ a ∈ R, a < k := by
          intro a ha
          have hle := hmax a (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))
          exact lt_of_le_of_ne hle (fun he => hkR (he ▸ ha))
        have hrsplit := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons] at hrsplit
        have hLt : L.length < n := by linarith only [hrsplit, hrs, Nat.zero_le R.length]
        have hRt : R.length < n := by linarith only [hrsplit, hrs, Nat.zero_le L.length]
        have hxlen : xs.length = (L.length + 1) + (R.length + 1) := by
          linarith only [hlen, hrsplit]
        have hcut : L.length + 1 ≤ xs.length := by linarith only [hxlen, Nat.zero_le R.length]
        have hleft : (xs.take (L.length + 1)).length = L.length + 1 := by
          rw [List.length_take, Nat.min_eq_left hcut]
        have hright : (xs.drop (L.length + 1)).length = R.length + 1 := by
          rw [List.length_drop, hxlen, Nat.add_sub_cancel_left]
        obtain ⟨l, hhl, hll, hgl⟩ := ih L.length hLt (xs.take (L.length + 1)) L rfl hleft hndL
        obtain ⟨r, hhr, hlr, hgr⟩ := ih R.length hRt (xs.drop (L.length + 1)) R rfl hright hndR
        refine ⟨.branch k l r, ⟨hhl, hhr, ?_, ?_⟩, ?_, ?_⟩
        · intro a ha
          rw [hgl] at ha
          exact hLmax a ha
        · intro a ha
          rw [hgr] at ha
          exact hRmax a ha
        · simp only [inorderLeaves, hll, hlr, List.take_append_drop]
        · simpa only [inorderGaps, hgl, hgr] using hsplit.symm
  exact go rs.length xs rs rfl hlen hnd

structure RawWord (α β : Type*) where
  leaves : List α
  gaps : List β
  length_eq : leaves.length = gaps.length + 1
  gaps_nodup : gaps.Nodup

def HeapTree := {t : PlaneTree α β // HeapOrdered t ∧ (inorderGaps t).Nodup}

def serialize (t : HeapTree (α := α) (β := β)) : RawWord α β :=
  ⟨inorderLeaves t.val, inorderGaps t.val, inorder_length t.val, t.property.2⟩

theorem serialize_bijective : Function.Bijective (serialize (α := α) (β := β)) := by
  constructor
  · intro t t' he
    apply Subtype.ext
    exact heap_inorder_injective t.val t'.val t.property.1 t'.property.1
      (congrArg RawWord.leaves he) (congrArg RawWord.gaps he)
  · intro w
    obtain ⟨t, ht, hl, hg⟩ := exists_heap_tree w.leaves w.gaps w.length_eq w.gaps_nodup
    have hnd : (inorderGaps t).Nodup := hg.symm ▸ w.gaps_nodup
    refine ⟨⟨t, ht, hnd⟩, ?_⟩
    cases w
    simp only [serialize] at hl hg ⊢
    cases hl
    cases hg
    rfl

/-- A genuine bijection between raw inorder words and the corresponding
plane Cartesian trees, before imposing anchor/permutation constraints. -/
noncomputable def heapTreeRawWordEquiv : HeapTree (α := α) (β := β) ≃ RawWord α β :=
  Equiv.ofBijective serialize serialize_bijective

#check @heap_inorder_injective
#check @exists_heap_tree
#check @heapTreeRawWordEquiv
#print axioms heap_inorder_injective
#print axioms exists_heap_tree
#print axioms heapTreeRawWordEquiv
end MaxCaterpillar.Frontier.RandomRestriction.Cartesian
