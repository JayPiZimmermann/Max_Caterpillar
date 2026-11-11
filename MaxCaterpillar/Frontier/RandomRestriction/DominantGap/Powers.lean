import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Choose

/-! # Exact dominance of the largest nonzero real-coefficient power

The coefficients are arbitrary real numbers. A direct finite Cauchy bound gives
a uniform real threshold, avoiding rationalization or a genericity hypothesis.
All finite families admit one common sufficiently large positive parameter.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators

noncomputable def powerSum {ι : Type*} [Fintype ι]
    (c : ι→ℝ) (e : ι→ℕ) (T : ℝ) : ℝ := ∑ i,c i*T^(e i)

/-- The largest exponent with a nonzero coefficient. -/
def Dominant {ι : Type*} (c : ι→ℝ) (e : ι→ℕ) (k : ι) : Prop :=
  c k≠0 ∧ ∀ i,c i≠0→i≠k→e i<e k

lemma dominant_unique {ι : Type*} {c : ι→ℝ} {e : ι→ℕ} {i j : ι}
    (hi : Dominant c e i) (hj : Dominant c e j) : i=j := by
  by_contra h
  exact (Nat.lt_asymm (hi.2 j hj.1 (Ne.symm h)) (hj.2 i hi.1 h))

lemma exists_dominant {ι : Type*} [Fintype ι] (c : ι→ℝ) (e : ι→ℕ)
    (he : Function.Injective e) (hc : ∃ i,c i≠0) : ∃ k,Dominant c e k := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => c i≠0
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := hc
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image s e hs
  refine ⟨k,(Finset.mem_filter.mp hk).2,?_⟩
  intro i hi hik
  have hle : e i≤e k := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact lt_of_le_of_ne hle (fun h => hik (he h))

lemma dominant_tail_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι→ℝ) (e : ι→ℕ) (k : ι)
    (hd : Dominant c e k) {T : ℝ} (hT : 1≤T) :
    |∑ i in Finset.univ.erase k,c i*T^(e i)|≤
      (∑ i in Finset.univ.erase k,|c i|)*T^(e k-1) := by
  classical
  calc
    _ ≤ ∑ i in Finset.univ.erase k,|c i*T^(e i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i in Finset.univ.erase k,|c i| *T^(e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul,abs_of_nonneg (pow_nonneg (le_trans zero_le_one hT) _)]
    _ ≤ ∑ i in Finset.univ.erase k,|c i| *T^(e k-1) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hc : c i=0
      · simp only [hc,abs_zero,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right hT (Nat.le_sub_one_of_lt
            (hd.2 i hc (Finset.mem_erase.mp hi).1))) (abs_nonneg _)
    _ = _ := Finset.sum_mul.symm

/-- Beyond an explicit finite threshold, the value has the sign of its highest
nonzero coefficient. No coefficient-size or arithmetic restriction is assumed. -/
theorem exists_dominant_threshold {ι : Type*} [Fintype ι]
    (c : ι→ℝ) (e : ι→ℕ) (k : ι) (hd : Dominant c e k) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→0<c k*powerSum c e T := by
  classical
  by_cases hdeg : e k=0
  · have hsum : ∀ T : ℝ,powerSum c e T=c k := by
      intro T
      unfold powerSum
      rw [Finset.sum_eq_single k]
      · rw [hdeg,pow_zero,mul_one]
      · intro i _ hik
        have hc : c i=0 := by
          by_contra hc
          have he := hd.2 i hc hik
          rw [hdeg] at he
          exact Nat.not_lt_zero _ he
        rw [hc,zero_mul]
      · intro hk
        exact False.elim (hk (Finset.mem_univ _))
    refine ⟨2,le_refl _,?_⟩
    intro T _
    rw [hsum]
    exact mul_self_pos.mpr hd.1
  · let S : ℝ := ∑ i in Finset.univ.erase k,|c i|
    let B : ℝ := max 2 (S/|c k|+1)
    refine ⟨B,le_max_left _ _,?_⟩
    intro T hBT
    have hT : 1≤T := le_trans (by norm_num : (1:ℝ)≤2)
      (le_trans (le_max_left _ _) hBT)
    have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
    have hlead : 0< |c k| := abs_pos.mpr hd.1
    have hdiv : S/|c k|<T := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hBT)
    have hS : S< |c k| *T := by
      have h := (div_lt_iff hlead).mp hdiv
      simpa only [mul_comm] using h
    have hp : 0<T^(e k-1) := pow_pos hTpos _
    have hsuc : e k-1+1=e k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hdeg)
    have hstrict : S*T^(e k-1)< |c k| *T^(e k) := by
      calc
        _ < (|c k| *T)*T^(e k-1) := mul_lt_mul_of_pos_right hS hp
        _ = |c k| *(T^(e k-1)*T) := by ring
        _ = _ := by rw [mul_comm (T^(e k-1)) T,← pow_succ,hsuc]
    have htail : |∑ i in Finset.univ.erase k,c i*T^(e i)|< |c k| *T^(e k) :=
      lt_of_le_of_lt (dominant_tail_bound c e k hd hT) hstrict
    have hsum : powerSum c e T=c k*T^(e k)+∑ i in Finset.univ.erase k,c i*T^(e i) := by
      unfold powerSum
      have h := Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun i => c i*T^(e i)) (Finset.mem_univ k)
      dsimp only at h
      linarith only [h]
    rw [hsum]
    rcases lt_or_gt_of_ne hd.1 with hn | hp
    · rw [abs_of_neg hn] at htail
      have htail' := le_abs_self (∑ i in Finset.univ.erase k,c i*T^(e i))
      have hval : c k*T^(e k)+(∑ i in Finset.univ.erase k,c i*T^(e i))<0 := by
        linarith only [htail,htail']
      exact mul_pos_of_neg_of_neg hn hval
    · rw [abs_of_pos hp] at htail
      have htail' := neg_abs_le_self (∑ i in Finset.univ.erase k,c i*T^(e i))
      have hval : 0<c k*T^(e k)+(∑ i in Finset.univ.erase k,c i*T^(e i)) := by
        linarith only [htail,htail']
      exact mul_pos hp hval

/-- Simultaneously records no accidental zero and the complete dominant sign. -/
def StableEvaluation {ι : Type*} [Fintype ι] (c : ι→ℝ) (e : ι→ℕ) (T : ℝ) : Prop :=
  (powerSum c e T=0↔∀ i,c i=0) ∧ ∀ k,Dominant c e k→0<c k*powerSum c e T

theorem exists_stable_threshold {ι : Type*} [Fintype ι]
    (c : ι→ℝ) (e : ι→ℕ) (he : Function.Injective e) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→StableEvaluation c e T := by
  classical
  by_cases hc : ∀ i,c i=0
  · refine ⟨2,le_refl _,?_⟩
    intro T _
    constructor
    · simp [powerSum,hc]
    · intro k hk
      exact False.elim (hk.1 (hc k))
  · have hn : ∃ i,c i≠0 := by simpa only [not_forall] using hc
    obtain ⟨k,hk⟩ := exists_dominant c e he hn
    obtain ⟨B,hB,hBT⟩ := exists_dominant_threshold c e k hk
    refine ⟨B,hB,?_⟩
    intro T hT
    have hpos := hBT T hT
    refine ⟨?_,?_⟩
    · constructor
      · intro hz
        rw [hz,mul_zero] at hpos
        exact False.elim (lt_irrefl _ hpos)
      · intro hall
        exact False.elim (hk.1 (hall k))
    · intro j hj
      rw [dominant_unique hj hk]
      exact hpos

/-- One common large real parameter works for finite families even when the
injective exponent assignment varies from one row/configuration to another. -/
theorem finite_family_shared_threshold_varying {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : κ→ι→ℝ) (e : κ→ι→ℕ) (he : ∀ a,Function.Injective (e a)) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ a,StableEvaluation (c a) (e a) T := by
  classical
  choose bound hbound hstable using fun a => exists_stable_threshold (c a) (e a) (he a)
  let B : ℝ := 2+∑ a,bound a
  have hnonneg : ∀ a,0≤bound a := fun a => le_trans (by norm_num) (hbound a)
  have hsum : 0≤∑ a,bound a := Finset.sum_nonneg (fun a _ => hnonneg a)
  refine ⟨B,by dsimp only [B]; linarith only [hsum],?_⟩
  intro T hT a
  apply hstable a T
  have ha : bound a≤∑ a,bound a := Finset.single_le_sum (fun b _ => hnonneg b) (Finset.mem_univ a)
  dsimp only [B] at hT
  linarith only [ha,hT]

/-- Common-exponent convenience form. -/
theorem finite_family_shared_threshold {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : κ→ι→ℝ) (e : ι→ℕ) (he : Function.Injective e) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ a,StableEvaluation (c a) e T :=
  finite_family_shared_threshold_varying c (fun _ => e) (fun _ => he)
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
