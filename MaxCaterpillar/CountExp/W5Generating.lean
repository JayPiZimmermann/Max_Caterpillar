import MaxCaterpillar.CountExp.Defs

/-!
# W5: the generating function at `x = 1/6` and coefficient extraction

* `pathWeight_le_one`: `∑_A 2^{-matchCount A} 6^{-|A|} ≤ 1` (step 6 of the main route
  in `research/sN/NOTE.md`).  Proof: a forward transfer argument along the spine.
  After spine index `q` the partial sum is weighted by the potential `1` when `q` has no
  link to the right, and otherwise by `7/9` when `s q` is outside `A` and not yet matched
  (it can still be matched to the right), and by `7/6` otherwise.
* `sum_card_eq_le_extract`: coefficient extraction with an injective size-decreasing map.
-/

open BigOperators Finset

namespace MaxCaterpillar.CountExp

section Generating

/-- Spine index `i` is not matched to its left neighbour by the greedy matching. -/
def prevFree (links A : Finset ℕ) : ℕ → Bool
  | 0 => true
  | i + 1 => !chosen links A i

theorem chosen_eq_prevFree (links A : Finset ℕ) (i : ℕ) :
    chosen links A i = (decide (i ∈ links ∧ i ∉ A ∧ i + 1 ∉ A) && prevFree links A i) := by
  cases i <;> simp [chosen, prevFree]

theorem chosen_congr (links A B : Finset ℕ) :
    ∀ i, (∀ j ≤ i + 1, (j ∈ A ↔ j ∈ B)) → chosen links A i = chosen links B i := by
  intro i
  induction i with
  | zero =>
    intro h
    simp only [chosen, h 0 (by omega), h 1 le_rfl]
  | succ i ih =>
    intro h
    have h1 := h (i + 1) (by omega)
    have h2 := h (i + 2) le_rfl
    have h3 := ih (fun j hj => h j (by omega))
    show (decide (i + 1 ∈ links ∧ i + 1 ∉ A ∧ i + 2 ∉ A) && !chosen links A i) =
      (decide (i + 1 ∈ links ∧ i + 1 ∉ B ∧ i + 2 ∉ B) && !chosen links B i)
    simp only [h1, h2, h3]

theorem card_filter_range_succ (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((range (n + 1)).filter p).card = ((range n).filter p).card + if p n then 1 else 0 := by
  rw [range_succ, filter_insert]
  split_ifs with h
  · rw [card_insert_of_not_mem]
    simp
  · simp

theorem matchCount_succ (q : ℕ) (links leafy A B : Finset ℕ)
    (hAB : ∀ j ≤ q, (j ∈ A ↔ j ∈ B)) :
    matchCount (q + 1) links leafy B =
      matchCount q links leafy A + (if chosen links B q = true then 1 else 0) +
        (if Single links (q + 1) ∧ q + 1 ∈ leafy ∧ q + 1 ∉ B then 1 else 0) := by
  unfold matchCount
  rw [card_filter_range_succ (fun i => chosen links B i = true) q,
    card_filter_range_succ (fun i => Single links i ∧ i ∈ leafy ∧ i ∉ B) (q + 1)]
  have e1 : (range q).filter (fun i => chosen links B i = true) =
      (range q).filter (fun i => chosen links A i = true) := by
    apply filter_congr
    intro i hi
    rw [mem_range] at hi
    rw [chosen_congr links A B i (fun j hj => hAB j (by omega))]
  have e2 : (range (q + 1)).filter (fun i => Single links i ∧ i ∈ leafy ∧ i ∉ B) =
      (range (q + 1)).filter (fun i => Single links i ∧ i ∈ leafy ∧ i ∉ A) := by
    apply filter_congr
    intro i hi
    rw [mem_range] at hi
    rw [hAB i (by omega)]
  rw [e1, e2]
  ring

theorem respects_succ (q : ℕ) (links leafy F A B : Finset ℕ)
    (hAB : ∀ j ≤ q, (j ∈ A ↔ j ∈ B)) :
    RespectsForced (q + 1) links leafy F B ↔
      RespectsForced q links leafy F A ∧
        (IsoSpine links leafy (q + 1) → (q + 1 ∈ B ↔ q + 1 ∈ F)) := by
  unfold RespectsForced
  rw [show range (q + 1 + 1) = insert (q + 1) (range (q + 1)) from range_succ,
    forall_mem_insert]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi hiso => ?_, h1⟩
    rw [hAB i (by rw [mem_range] at hi; omega)]
    exact h2 i hi hiso
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun i hi hiso => ?_⟩
    rw [← hAB i (by rw [mem_range] at hi; omega)]
    exact h1 i hi hiso

/-- The potential-weighted term of the transfer argument. -/
def pot (q : ℕ) (links leafy A : Finset ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ matchCount q links leafy A * (1 / 6 : ℚ) ^ A.card *
    (if q ∈ links then (if q ∉ A ∧ prevFree links A q = true then 7 / 9 else 7 / 6) else 1)

/-- The one-step inequality of the transfer argument. -/
theorem local_ineq (L L' av lf inF : Prop) [Decidable L] [Decidable L'] [Decidable av]
    [Decidable lf] [Decidable inF] :
    (if ((¬L ∧ ¬L') ∧ ¬lf → (¬inF)) then
        (1 / 2 : ℚ) ^ (if L ∧ av then 1 else 0) * (1 / 2 : ℚ) ^ (if (¬L ∧ ¬L') ∧ lf then 1 else 0) *
          (if L' then (if ¬(L ∧ av) then 7 / 9 else 7 / 6) else 1)
      else 0) +
      (if ((¬L ∧ ¬L') ∧ ¬lf → inF) then (1 / 6 : ℚ) * (if L' then 7 / 6 else 1) else 0) ≤
      (if L then (if av then 7 / 9 else 7 / 6) else 1) := by
  by_cases hL : L <;> by_cases hL' : L' <;> by_cases hav : av <;> by_cases hlf : lf <;>
    by_cases hF : inF <;> simp [hL, hL', hav, hlf, hF] <;> norm_num

theorem step_term (q : ℕ) (links leafy F A : Finset ℕ) (hA : A ⊆ range (q + 1))
    (hRF : RespectsForced q links leafy F A) :
    (if RespectsForced (q + 1) links leafy F A then pot (q + 1) links leafy A else 0) +
      (if RespectsForced (q + 1) links leafy F (insert (q + 1) A) then
        pot (q + 1) links leafy (insert (q + 1) A) else 0) ≤ pot q links leafy A := by
  have hq1 : q + 1 ∉ A := fun h => by have := hA h; simp at this
  have hAA : ∀ j ≤ q, (j ∈ A ↔ j ∈ A) := fun _ _ => Iff.rfl
  have hAI : ∀ j ≤ q, (j ∈ A ↔ j ∈ insert (q + 1) A) := fun j hj => by
    simp [show j ≠ q + 1 by omega]
  simp only [respects_succ q links leafy F A A hAA, respects_succ q links leafy F A _ hAI, hRF,
    true_and]
  unfold pot
  rw [matchCount_succ q links leafy A A hAA, matchCount_succ q links leafy A _ hAI,
    card_insert_of_not_mem hq1]
  have hch : chosen links (insert (q + 1) A) q = false := by cases q <;> simp [chosen]
  have hchA : chosen links A q =
      decide (q ∈ links ∧ (q ∉ A ∧ prevFree links A q = true)) := by
    rw [chosen_eq_prevFree]
    by_cases h1 : q ∈ links <;> by_cases h2 : q ∈ A <;> cases prevFree links A q <;>
      simp [h1, h2, hq1]
  have hpf : ∀ B, prevFree links B (q + 1) = !chosen links B q := fun B => rfl
  have hsingle : Single links (q + 1) ↔ (¬ q ∈ links ∧ ¬ q + 1 ∈ links) := by simp [Single]
  have hiso : IsoSpine links leafy (q + 1) ↔
      ((¬ q ∈ links ∧ ¬ q + 1 ∈ links) ∧ ¬ q + 1 ∈ leafy) := by
    simp [IsoSpine, hsingle]
  simp only [hpf, hch, hiso, hsingle, hchA, mem_insert_self, not_true, hq1, not_false_eq_true,
    true_and, and_true, false_and, and_false]
  have ha : 0 ≤ (1 / 2 : ℚ) ^ matchCount q links leafy A := by positivity
  have hb : 0 ≤ (1 / 6 : ℚ) ^ A.card := by positivity
  simp only [pow_add]
  generalize (1 / 2 : ℚ) ^ matchCount q links leafy A = a at ha ⊢
  generalize (1 / 6 : ℚ) ^ A.card = b at hb ⊢
  have hab := mul_nonneg ha hb
  by_cases hL : q ∈ links <;> by_cases hL' : q + 1 ∈ links <;>
    by_cases hav : (q ∉ A ∧ prevFree links A q = true) <;> by_cases hlf : q + 1 ∈ leafy <;>
    by_cases hF : q + 1 ∈ F <;>
    (try simp only [eq_true hL]) <;> (try simp only [eq_false hL]) <;>
    (try simp only [eq_true hL']) <;> (try simp only [eq_false hL']) <;>
    (try simp only [eq_true hav]) <;> (try simp only [eq_false hav]) <;>
    (try simp only [eq_true hlf]) <;> (try simp only [eq_false hlf]) <;>
    (try simp only [eq_true hF]) <;> (try simp only [eq_false hF]) <;>
    norm_num <;> nlinarith [hab]

/-- The transfer invariant: the potential-weighted sum over the admissible sets of
`{0, …, q}` is at most `1`. -/
theorem pot_sum_le (links leafy F : Finset ℕ) :
    ∀ q, ∑ A in admissibleIdx q links leafy F, pot q links leafy A ≤ 1 := by
  intro q
  induction q with
  | zero =>
    unfold admissibleIdx
    rw [sum_filter, show range (0 + 1) = insert 0 (range 0) from range_succ,
      sum_powerset_insert (by simp)]
    simp only [range_zero, powerset_empty, sum_singleton, insert_emptyc_eq]
    by_cases hL : 0 ∈ links <;> by_cases hlf : 0 ∈ leafy <;> by_cases hF : 0 ∈ F <;>
      simp [RespectsForced, IsoSpine, Single, matchCount, pot, prevFree, hL, hlf, hF] <;>
      norm_num
  | succ q ih =>
    unfold admissibleIdx
    rw [sum_filter, show range (q + 1 + 1) = insert (q + 1) (range (q + 1)) from range_succ,
      sum_powerset_insert (by simp), ← sum_add_distrib]
    calc _ ≤ ∑ A in (range (q + 1)).powerset,
          if RespectsForced q links leafy F A then pot q links leafy A else 0 := by
          apply sum_le_sum
          intro A hA
          rw [mem_powerset] at hA
          have hAA : ∀ j ≤ q, (j ∈ A ↔ j ∈ A) := fun _ _ => Iff.rfl
          have hAI : ∀ j ≤ q, (j ∈ A ↔ j ∈ insert (q + 1) A) := fun j hj => by
            simp [show j ≠ q + 1 by omega]
          by_cases hRF : RespectsForced q links leafy F A
          · rw [if_pos hRF]
            exact step_term q links leafy F A hA hRF
          · rw [if_neg hRF]
            simp only [respects_succ q links leafy F A A hAA,
              respects_succ q links leafy F A _ hAI, hRF, false_and, if_false]
            norm_num
      _ = ∑ A in admissibleIdx q links leafy F, pot q links leafy A := by
          rw [admissibleIdx, sum_filter]
      _ ≤ 1 := ih

theorem pathWeight_le_one (q : ℕ) (links leafy F : Finset ℕ) (hlinks : links ⊆ range q) :
    pathWeight q links leafy F (1 / 6) ≤ 1 := by
  have hq : q ∉ links := fun h => by have := hlinks h; simp at this
  calc pathWeight q links leafy F (1 / 6)
        = ∑ A in admissibleIdx q links leafy F, pot q links leafy A := by
          unfold pathWeight
          refine sum_congr rfl fun A _ => ?_
          simp [pot, hq]
    _ ≤ 1 := pot_sum_le links leafy F q

/-- Coefficient extraction: with an injective size-decreasing index map,
`∑_{|T| = k} g(f T) ≤ 6^k ∑_A g(A) 6^{-|A|}`. -/
theorem sum_card_eq_le_extract {α : Type*} [DecidableEq α] (S : Finset (Finset α))
    (f : Finset α → Finset ℕ) (hf : Set.InjOn f S) (hcard : ∀ T ∈ S, (f T).card ≤ T.card)
    (g : Finset ℕ → ℚ) (hg : ∀ A, 0 ≤ g A) (k : ℕ) :
    ∑ T in S.filter (fun T => T.card = k), g (f T) ≤
      6 ^ k * ∑ A in S.image f, g A * (1 / 6) ^ A.card := by
  calc ∑ T in S.filter (fun T => T.card = k), g (f T)
        ≤ ∑ T in S.filter (fun T => T.card = k), 6 ^ k * (g (f T) * (1 / 6) ^ (f T).card) := by
          apply sum_le_sum
          intro T hT
          rw [mem_filter] at hT
          have hle : (1 / 6 : ℚ) ^ k ≤ (1 / 6) ^ (f T).card :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (hT.2 ▸ hcard T hT.1)
          have h1 : (6 : ℚ) ^ k * (1 / 6) ^ k = 1 := by rw [← mul_pow]; norm_num
          have hpos : (0 : ℚ) ≤ 6 ^ k := by positivity
          calc g (f T) = g (f T) * (6 ^ k * (1 / 6) ^ k) := by rw [h1, mul_one]
            _ ≤ g (f T) * (6 ^ k * (1 / 6) ^ (f T).card) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hpos) (hg _)
            _ = 6 ^ k * (g (f T) * (1 / 6) ^ (f T).card) := by ring
    _ ≤ ∑ T in S, 6 ^ k * (g (f T) * (1 / 6) ^ (f T).card) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun T _ _ =>
            mul_nonneg (by positivity) (mul_nonneg (hg _) (by positivity))
    _ = 6 ^ k * ∑ A in S.image f, g A * (1 / 6) ^ A.card := by
          rw [← mul_sum, sum_image fun x hx y hy h => hf (mem_coe.2 hx) (mem_coe.2 hy) h]

end Generating

end MaxCaterpillar.CountExp
