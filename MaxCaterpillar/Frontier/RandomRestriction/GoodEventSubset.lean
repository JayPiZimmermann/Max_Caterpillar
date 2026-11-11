import Mathlib
import Mathlib.Combinatorics.DoubleCounting

/-!
# Uniform rank-permutation inclusion bounds

The probability space is the finite set of all permutations of `Fin m`.
The selected gaps are exactly those whose permuted rank is less than `K`.
No independence or subset-distribution hypothesis is imposed.
-/
set_option autoImplicit false
open scoped BigOperators

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent

noncomputable def smallRankGaps {m : ℕ} (ρ : Equiv.Perm (Fin m)) (K : ℕ) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun g => (ρ g).val < K

noncomputable def containmentEvent {m : ℕ} (K : ℕ) (I : Finset (Fin m)) :
    Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun ρ => I ⊆ smallRankGaps ρ K

@[simp] theorem mem_smallRankGaps {m K : ℕ} (ρ : Equiv.Perm (Fin m)) (g : Fin m) :
    g ∈ smallRankGaps ρ K ↔ (ρ g).val < K := by
  classical
  simp [smallRankGaps]

@[simp] theorem mem_containmentEvent {m K : ℕ} (I : Finset (Fin m))
    (ρ : Equiv.Perm (Fin m)) :
    ρ ∈ containmentEvent K I ↔ I ⊆ smallRankGaps ρ K := by
  classical
  simp [containmentEvent]

theorem card_smallRankGaps {m K : ℕ} (hKm : K ≤ m) (ρ : Equiv.Perm (Fin m)) :
    (smallRankGaps ρ K).card = K := by
  classical
  have himage : (smallRankGaps ρ K).image ρ =
      Finset.univ.filter (fun v : Fin m => v.val < K) := by
    ext v
    simp only [Finset.mem_image, mem_smallRankGaps, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hv
      exact ⟨ρ.symm v, by simpa using hv, by simp⟩
  have hc := Finset.card_image_of_injective (smallRankGaps ρ K) ρ.injective
  rw [himage] at hc
  rw [← hc]
  rcases lt_or_eq_of_le hKm with hlt | heqKm
  · have heq : Finset.univ.filter (fun v : Fin m => v.val < K) =
        Finset.Iio (⟨K, hlt⟩ : Fin m) := by
      ext v
      simp [Fin.lt_def]
    rw [heq, Fin.card_Iio]
  · subst K
    have heq : Finset.univ.filter (fun v : Fin m => v.val < m) = Finset.univ := by
      ext v
      simp [v.isLt]
    simp [heq]

private theorem swap_preserves_insert_event {m K : ℕ} (I : Finset (Fin m))
    (a g : Fin m) (ha : a ∉ I) (hg : g ∉ I) (ρ : Equiv.Perm (Fin m)) :
    ρ ∈ containmentEvent K (insert a I) ↔
      (Equiv.swap a g).trans ρ ∈ containmentEvent K (insert g I) := by
  classical
  simp only [mem_containmentEvent, Finset.insert_subset_iff]
  have hfix : ∀ x ∈ I, Equiv.swap a g x = x := by
    intro x hx
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; exact ha (h ▸ hx)
    · intro h; exact hg (h ▸ hx)
  simp only [mem_smallRankGaps, Equiv.trans_apply, Equiv.swap_apply_right]
  have heq : I ⊆ smallRankGaps ρ K ↔
      I ⊆ smallRankGaps ((Equiv.swap a g).trans ρ) K := by
    constructor <;> intro h x hx <;> specialize h hx
    · simpa only [mem_smallRankGaps, Equiv.trans_apply, hfix x hx] using h
    · simpa only [mem_smallRankGaps, Equiv.trans_apply, hfix x hx] using h
  rw [heq]

theorem card_insert_event_eq {m K : ℕ} (I : Finset (Fin m)) (a g : Fin m)
    (ha : a ∉ I) (hg : g ∉ I) :
    (containmentEvent K (insert a I)).card =
      (containmentEvent K (insert g I)).card := by
  classical
  apply Finset.card_congr (fun ρ _ => (Equiv.swap a g).trans ρ)
  · intro ρ hρ
    exact (swap_preserves_insert_event I a g ha hg ρ).mp hρ
  · intro ρ σ _ _ heq
    apply Equiv.ext
    intro x
    have h := congrArg (fun e : Equiv.Perm (Fin m) => e (Equiv.swap a g x)) heq
    simpa only [Equiv.trans_apply, Equiv.swap_apply_self] using h
  · intro σ hσ
    let ρ := (Equiv.swap a g).trans σ
    have hinv : (Equiv.swap a g).trans ρ = σ := by
      ext x
      simp [ρ]
    refine ⟨ρ, ?_, hinv⟩
    apply (swap_preserves_insert_event I a g ha hg ρ).mpr
    rw [hinv]
    exact hσ

/-- A single additional requested gap costs at most the marginal `K/m`.
This follows from actual permutation swaps and double counting, even when
the conditioning event is empty. -/
theorem card_insert_event_mul_le {m K : ℕ} (hKm : K ≤ m)
    (I : Finset (Fin m)) (a : Fin m) (ha : a ∉ I) :
    m * (containmentEvent K (insert a I)).card ≤
      K * (containmentEvent K I).card := by
  classical
  have habove (g : Fin m) :
      ((containmentEvent K I).bipartiteAbove
        (fun g ρ => g ∈ smallRankGaps ρ K) g) =
        containmentEvent K (insert g I) := by
    ext ρ
    simp [Finset.bipartiteAbove, Finset.insert_subset_iff, and_comm]
  have hbelow (ρ : Equiv.Perm (Fin m)) :
      (Finset.univ.bipartiteBelow (fun g ρ => g ∈ smallRankGaps ρ K) ρ) =
        smallRankGaps ρ K := by
    ext g
    simp [Finset.bipartiteBelow]
  have hc := Finset.card_mul_le_card_mul
    (fun (g : Fin m) (ρ : Equiv.Perm (Fin m)) => g ∈ smallRankGaps ρ K)
    (s := Finset.univ) (t := containmentEvent K I)
    (m := (containmentEvent K (insert a I)).card) (n := K)
    (by
      intro g _
      rw [habove]
      by_cases hg : g ∈ I
      · rw [Finset.insert_eq_of_mem hg]
        apply Finset.card_le_of_subset
        intro ρ hρ
        exact (mem_containmentEvent I ρ).mpr
          (fun x hx => ((mem_containmentEvent (insert a I) ρ).mp hρ)
            (Finset.mem_insert_of_mem hx))
      · exact le_of_eq (card_insert_event_eq I a g ha hg))
    (by intro ρ _; rw [hbelow, card_smallRankGaps hKm])
  simpa only [Finset.card_univ, Fintype.card_fin, mul_comm] using hc

/-- Integer counting form, with no denominator or nonemptiness assumption. -/
theorem containment_card_mul_pow_le {m K : ℕ} (hKm : K ≤ m)
    (I : Finset (Fin m)) :
    (containmentEvent K I).card * m ^ I.card ≤
      Fintype.card (Equiv.Perm (Fin m)) * K ^ I.card := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have he : containmentEvent K (∅ : Finset (Fin m)) = Finset.univ := by
      ext ρ
      simp
    rw [he]
    simp only [Finset.card_empty, pow_zero, mul_one, Finset.card_univ]
    exact le_rfl
  | @insert a I ha ih =>
    rw [Finset.card_insert_of_not_mem ha, pow_succ, pow_succ]
    have hs := Nat.mul_le_mul_right (m ^ I.card)
      (card_insert_event_mul_le hKm I a ha)
    have hi := Nat.mul_le_mul_left K ih
    nlinarith only [hs, hi]

/-- Uniform probability on all rank permutations. In particular, no
independence of the selected-gap indicators is assumed. -/
theorem containment_fraction_le {m K : ℕ} (hm : 0 < m) (hKm : K ≤ m)
    (I : Finset (Fin m)) :
    ((containmentEvent K I).card : ℝ) / Fintype.card (Equiv.Perm (Fin m)) ≤
      ((K : ℝ) / m) ^ I.card := by
  have hi : ((containmentEvent K I).card : ℝ) * (m : ℝ) ^ I.card ≤
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * (K : ℝ) ^ I.card := by
    exact_mod_cast containment_card_mul_pow_le hKm I
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin m)⟩
  rw [div_pow]
  apply (div_le_div_iff hp (pow_pos hm' _)).mpr
  simpa only [mul_comm] using hi

theorem containment_event_empty_of_card_gt {m K : ℕ} (hKm : K ≤ m)
    (I : Finset (Fin m)) (hI : K < I.card) : containmentEvent K I = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro ρ hρ
  have hc := Finset.card_le_of_subset ((mem_containmentEvent I ρ).mp hρ)
  rw [card_smallRankGaps hKm] at hc
  exact (not_le_of_gt hI) hc

/-- The same probability statement with the actual permutation event exposed. -/
theorem subset_smallRankGaps_fraction_le {m K : ℕ} (hm : 0 < m) (hKm : K ≤ m)
    (I : Finset (Fin m)) :
    ((Finset.univ.filter (fun ρ : Equiv.Perm (Fin m) =>
        I ⊆ smallRankGaps ρ K)).card : ℝ) /
        Fintype.card (Equiv.Perm (Fin m)) ≤ ((K : ℝ) / m) ^ I.card := by
  classical
  exact containment_fraction_le hm hKm I

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
