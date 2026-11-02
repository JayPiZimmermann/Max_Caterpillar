import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-!
# Exact finite coin uniformity from single-bit flip equivalences

The state space is finite. Each flip preserves the recorded data and changes
exactly its designated coin. These actual state-space equivalences imply equal
cardinalities of all full coin-pattern fibers inside every data fiber. No
commutation assumption on the state-space flips occurs.

Actual Cartesian-tree configurations and their block-swap maps are not defined
in this file. Applying the theorem to them requires constructing the displayed
equivalences and verifying both fields of `CoinFlipSystem`.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators

variable {ι Ω Data : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def flipBit (i : ι) (b : ι → Bool) : ι → Bool :=
  fun j => if j = i then !(b j) else b j

lemma flipBit_involutive (i : ι) : Function.Involutive (flipBit i) := by
  intro b
  funext j
  by_cases hj : j = i <;> simp [flipBit, hj]

lemma flipBit_injective (i : ι) : Function.Injective (flipBit i) :=
  (flipBit_involutive i).injective

/-- Genuine equivalences of the underlying finite state space, preserving
the data and flipping only one specified bit. -/
structure CoinFlipSystem (recorded : Ω → Data) (coins : Ω → ι → Bool) where
  equiv : ι → Ω ≃ Ω
  data_eq : ∀ i ω, recorded (equiv i ω) = recorded ω
  coins_eq : ∀ i ω, coins (equiv i ω) = flipBit i (coins ω)

noncomputable def dataFiber (recorded : Ω → Data) (d : Data) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => recorded ω = d

noncomputable def patternFiber (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (d : Data) (b : ι → Bool) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => recorded ω = d ∧ coins ω = b

noncomputable def coinEventFiber (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (d : Data) (B : Finset (ι → Bool)) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => recorded ω = d ∧ coins ω ∈ B

@[simp] lemma mem_dataFiber (recorded : Ω → Data) (d : Data) (ω : Ω) :
    ω ∈ dataFiber recorded d ↔ recorded ω = d := by
  classical
  simp only [dataFiber, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] lemma mem_patternFiber (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (d : Data) (b : ι → Bool) (ω : Ω) :
    ω ∈ patternFiber recorded coins d b ↔ recorded ω = d ∧ coins ω = b := by
  classical
  simp only [patternFiber, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] lemma mem_coinEventFiber (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (d : Data) (B : Finset (ι → Bool)) (ω : Ω) :
    ω ∈ coinEventFiber recorded coins d B ↔ recorded ω = d ∧ coins ω ∈ B := by
  classical
  simp only [coinEventFiber, Finset.mem_filter, Finset.mem_univ, true_and]

lemma pattern_card_flip (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data) (i : ι) (b : ι → Bool) :
    (patternFiber recorded coins d b).card =
      (patternFiber recorded coins d (flipBit i b)).card := by
  classical
  apply Finset.card_congr (fun ω _ => system.equiv i ω)
  · intro ω hω
    rcases mem_patternFiber recorded coins d b ω |>.mp hω with ⟨hd, hb⟩
    exact (mem_patternFiber _ _ _ _ _).mpr
      ⟨(system.data_eq i ω).trans hd, (system.coins_eq i ω).trans (congrArg (flipBit i) hb)⟩
  · intro ω ω' _ _ h
    exact (system.equiv i).injective h
  · intro ω hω
    refine ⟨(system.equiv i).symm ω, ?_, (system.equiv i).apply_symm_apply ω⟩
    rcases (mem_patternFiber _ _ _ _ _).mp hω with ⟨hd, hb⟩
    apply (mem_patternFiber _ _ _ _ _).mpr
    constructor
    · have h := system.data_eq i ((system.equiv i).symm ω)
      rw [(system.equiv i).apply_symm_apply] at h
      exact h.symm.trans hd
    · apply flipBit_injective i
      have h := system.coins_eq i ((system.equiv i).symm ω)
      rw [(system.equiv i).apply_symm_apply] at h
      exact h.symm.trans hb

/-- Every function on a finite Boolean cube invariant under the single-bit
flips is constant. This does not compose, or compare, state-space flips. -/
lemma eq_of_single_bit_flips {A : Type*} (F : (ι → Bool) → A)
    (hflip : ∀ i b, F (flipBit i b) = F b) (a b : ι → Bool) : F a = F b := by
  classical
  have go : ∀ s : Finset ι, ∀ a b : ι → Bool,
      (∀ j, j ∉ s → a j = b j) → F a = F b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a b hab
      have he : a = b := funext fun j => hab j (Finset.not_mem_empty j)
      rw [he]
    | @insert i s _hi ih =>
      intro a b hab
      let c : ι → Bool := fun j => if j = i then b j else a j
      have hac : F a = F c := by
        by_cases he : a i = b i
        · have hc : c = a := by
            funext j
            by_cases hj : j = i
            · subst j
              simp only [c, if_pos rfl, he]
            · simp only [c, if_neg hj]
          rw [hc]
        · have hc : c = flipBit i a := by
            funext j
            by_cases hj : j = i
            · subst j
              simp only [c, flipBit, if_pos rfl]
              cases ha : a i <;> cases hb : b i <;> simp_all
            · simp only [c, flipBit, if_neg hj]
          rw [hc]
          exact (hflip i a).symm
      apply hac.trans
      apply ih c b
      intro j hj
      by_cases hji : j = i
      · simp only [c, if_pos hji]
      · have hnot : j ∉ insert i s := by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩
        simp only [c, if_neg hji]
        exact hab j hnot
  exact go Finset.univ a b (fun j hj => False.elim (hj (Finset.mem_univ j)))

/-- All full coin-pattern fibers in any fixed data fiber have equal size,
including empty data fibers. -/
theorem coin_pattern_cards_equal (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data) (a b : ι → Bool) :
    (patternFiber recorded coins d a).card = (patternFiber recorded coins d b).card := by
  apply eq_of_single_bit_flips (fun b => (patternFiber recorded coins d b).card)
    (fun i b => (pattern_card_flip recorded coins system d i b).symm) a b

/-- Exact joint uniformity: each coin pattern occurs exactly a 2^(-|ι|)
fraction of a nonempty data fiber. The integer equation also covers emptiness. -/
theorem data_fiber_card_eq (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data) (b : ι → Bool) :
    (dataFiber recorded d).card =
      2 ^ Fintype.card ι * (patternFiber recorded coins d b).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := dataFiber recorded d)
    (t := Finset.univ) (f := coins) (fun ω _ => Finset.mem_univ (coins ω))
  calc
    _ = ∑ a : ι → Bool, (patternFiber recorded coins d a).card := by
      rw [h]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      ext ω
      simp only [Finset.mem_filter, mem_dataFiber, mem_patternFiber]
    _ = ∑ _a : ι → Bool, (patternFiber recorded coins d b).card :=
      Finset.sum_congr rfl fun a _ => coin_pattern_cards_equal recorded coins system d a b
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Nat.cast_id]

/-- Every set of coin patterns has exactly its uniform fraction of each
data fiber. This supports arbitrary events, not only individual patterns. -/
theorem coin_event_card_eq (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data) (B : Finset (ι → Bool))
    (b : ι → Bool) :
    (coinEventFiber recorded coins d B).card =
      B.card * (patternFiber recorded coins d b).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := coinEventFiber recorded coins d B)
    (t := B) (f := coins) (fun ω hω => ((mem_coinEventFiber _ _ _ _ _).mp hω).2)
  calc
    _ = ∑ a in B, (patternFiber recorded coins d a).card := by
      rw [h]
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ext ω
      simp only [Finset.mem_filter, mem_coinEventFiber, mem_patternFiber]
      constructor
      · intro h
        exact ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2.symm ▸ ha⟩, h.2⟩
    _ = ∑ _a in B, (patternFiber recorded coins d b).card :=
      Finset.sum_congr rfl fun a _ => coin_pattern_cards_equal recorded coins system d a b
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

theorem coin_event_card_mul (recorded : Ω → Data) (coins : Ω → ι → Bool)
    (system : CoinFlipSystem recorded coins) (d : Data) (B : Finset (ι → Bool)) :
    (coinEventFiber recorded coins d B).card * 2 ^ Fintype.card ι =
      B.card * (dataFiber recorded d).card := by
  let b : ι → Bool := fun _ => false
  rw [coin_event_card_eq recorded coins system d B b,
    data_fiber_card_eq recorded coins system d b]
  ring

#check @CoinFlipSystem
#check @coin_pattern_cards_equal
#check @data_fiber_card_eq
#check @coin_event_card_eq
#check @coin_event_card_mul
#print axioms coin_pattern_cards_equal
#print axioms data_fiber_card_eq
#print axioms coin_event_card_eq
#print axioms coin_event_card_mul
end MaxCaterpillar.Frontier.RandomRestriction
