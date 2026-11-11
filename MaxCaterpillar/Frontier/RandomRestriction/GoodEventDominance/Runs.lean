import MaxCaterpillar.Frontier.RandomRestriction.GoodEventGeometry
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.PrefixSwap

/-! # Actual prefix cuts force cancellation on every gap run

The zero-sum statements are derived from vanishing prefixes at the unselected
gaps, including the actual full-tail boundary. They are not partition axioms.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
open BigOperators GoodEvent Cartesian DominantGap

variable {m : ℕ}
attribute [local instance] Classical.propDecidable

/-- Runs have exactly the same sides of every forbidden gap cut. -/
theorem tailSameRun_iff_forbiddenCuts (Γ : Finset (Fin m)) (a b : Fin m) :
    TailSameRun Γ a b ↔ ∀ g ∉ Γ,(a<g ↔ b<g) := by
  constructor
  · intro h g hg
    constructor
    · intro ha
      by_contra hb
      have hm : g∈tailInterval a b := Finset.mem_Ioc.mpr
        ⟨lt_of_le_of_lt (min_le_left a b) ha,le_trans (not_lt.mp hb) (le_max_right a b)⟩
      exact hg (h hm)
    · intro hb
      by_contra ha
      have hm : g∈tailInterval a b := Finset.mem_Ioc.mpr
        ⟨lt_of_le_of_lt (min_le_right a b) hb,le_trans (not_lt.mp ha) (le_max_left a b)⟩
      exact hg (h hm)
  · intro h g hg
    by_contra hnot
    have hs := h g hnot
    have hh := Finset.mem_Ioc.mp hg
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab,max_eq_right hab] at hh
      exact (not_lt_of_ge hh.2) (hs.mp hh.1)
    · rw [min_eq_right hba,max_eq_left hba] at hh
      exact (not_lt_of_ge hh.2) (hs.mpr hh.1)

theorem tailSameRun_refl (Γ : Finset (Fin m)) (a : Fin m) : TailSameRun Γ a a :=
  (tailSameRun_iff_forbiddenCuts Γ a a).mpr (fun _ _ => Iff.rfl)

/-- The actual interval-run relation is symmetric. -/
theorem tailSameRun_symm (Γ : Finset (Fin m)) {a b : Fin m}
    (h : TailSameRun Γ a b) : TailSameRun Γ b a := by
  apply (tailSameRun_iff_forbiddenCuts Γ b a).mpr
  intro g hg
  exact ((tailSameRun_iff_forbiddenCuts Γ a b).mp h g hg).symm

/-- The actual interval-run relation is transitive. -/
theorem tailSameRun_trans (Γ : Finset (Fin m)) {a b c : Fin m}
    (hab : TailSameRun Γ a b) (hbc : TailSameRun Γ b c) : TailSameRun Γ a c := by
  apply (tailSameRun_iff_forbiddenCuts Γ a c).mpr
  intro g hg
  exact ((tailSameRun_iff_forbiddenCuts Γ a b).mp hab g hg).trans
    ((tailSameRun_iff_forbiddenCuts Γ b c).mp hbc g hg)

theorem tailSameRun_selected_neighbor (Γ : Finset (Fin m)) (z a b : Fin m)
    (hab : a.val+1=b.val) (hb : b∈Γ) :
    TailSameRun Γ z a ↔ TailSameRun Γ z b := by
  have hside (g : Fin m) (hg : g∉Γ) : a<g ↔ b<g := by
    constructor
    · intro ha
      change a.val<g.val at ha
      change b.val<g.val
      by_contra hn
      have hgb : g.val≤b.val := not_lt.mp hn
      have hag : a.val+1≤g.val := Nat.succ_le_iff.mpr ha
      have he : g=b := Fin.ext (by linarith only [hab,hgb,hag])
      exact hg (he.symm ▸ hb)
    · intro hbg
      change a.val<g.val
      change b.val<g.val at hbg
      linarith only [hab,hbg]
  rw [tailSameRun_iff_forbiddenCuts,tailSameRun_iff_forbiddenCuts]
  exact ⟨fun h g hg => (h g hg).trans (hside g hg),
    fun h g hg => (h g hg).trans (hside g hg).symm⟩

noncomputable def runPositions (Γ : Finset (Fin m)) (z : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => TailSameRun Γ z k)

@[simp] theorem mem_runPositions (Γ : Finset (Fin m)) (z k : Fin m) :
    k∈runPositions Γ z ↔ TailSameRun Γ z k := by
  classical
  simp [runPositions]

private theorem run_sum_boundary (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (Γ : Finset (Fin m)) (hzero : (∑ x,w x)=0)
    (hcuts : ∀ g∉Γ,prefixCoeff p w g.val=0) (z : Fin m) :
    let hm : 0<m := lt_of_le_of_lt (Nat.zero_le z.val) z.isLt
    (∑ k in runPositions Γ z,w (some (p.1 k))) =
      -(if TailSameRun Γ z ⟨0,hm⟩ then w none else 0) := by
  classical
  let hm : 0<m := lt_of_le_of_lt (Nat.zero_le z.val) z.isLt
  let R : ℕ→ℝ := fun n => if hn : n<m then
    if TailSameRun Γ z ⟨n,hn⟩ then prefixCoeff p w n else 0 else 0
  have hval (k : Fin m) : R k.val=
      if TailSameRun Γ z k then prefixCoeff p w k.val else 0 := by
    simp only [R,dif_pos k.isLt]
  have hnext (k : Fin m) : R (k.val+1)=
      if TailSameRun Γ z k then prefixCoeff p w (k.val+1) else 0 := by
    by_cases hn : k.val+1<m
    · let b : Fin m := ⟨k.val+1,hn⟩
      by_cases hb : b∈Γ
      · have he := tailSameRun_selected_neighbor Γ z k b rfl hb
        simp only [R,dif_pos hn]
        change (if TailSameRun Γ z b then _ else 0)=_
        rw [← he]
      · have hz := hcuts b hb
        change prefixCoeff p w (k.val+1)=0 at hz
        simp only [R,dif_pos hn,hz,ite_self]
    · have he : k.val+1=m := by
        have hk := Nat.succ_le_of_lt k.isLt
        exact Nat.le_antisymm hk (not_lt.mp hn)
      have hz : prefixCoeff p w (k.val+1)=0 := by rw [he,prefixCoeff_at_card,hzero]
      simp only [R,dif_neg hn,hz,ite_self]
  have hterm (k : Fin m) : (if TailSameRun Γ z k then w (some (p.1 k)) else 0)=
      R (k.val+1)-R k.val := by
    rw [hnext,hval,prefixCoeff_succ]
    by_cases hk : TailSameRun Γ z k <;> simp [hk]
  have hsum : (∑ k in runPositions Γ z,w (some (p.1 k)))=R m-R 0 := by
    rw [runPositions,Finset.sum_filter]
    calc
      _ = ∑ k : Fin m,(R (k.val+1)-R k.val) := Finset.sum_congr rfl (fun k _ => hterm k)
      _ = ∑ k in Finset.range m,(R (k+1)-R k) := Fin.sum_univ_eq_sum_range (fun n => R (n+1)-R n) m
      _ = _ := Finset.sum_range_sub R m
  have hrm : R m=0 := by simp [R]
  have hr0 : R 0=(if TailSameRun Γ z ⟨0,hm⟩ then w none else 0) := by
    simp [R,hm,prefixCoeff]
  change (∑ k in runPositions Γ z,w (some (p.1 k))) = _
  rw [hsum,hrm,hr0,zero_sub]

private theorem anchor_implies_zero_run (Γ : Finset (Fin m)) (z : Fin m)
    (hm : 0<m) (h : AnchorSameRun Γ z) : TailSameRun Γ z ⟨0,hm⟩ := by
  intro g hg
  have hh := Finset.mem_Ioc.mp hg
  have hz : g≤z := by
    have he : max z (⟨0,hm⟩ : Fin m)=z := max_eq_left (show (⟨0,hm⟩ : Fin m)≤z from Nat.zero_le z.val)
    rw [he] at hh
    exact hh.2
  exact h (Finset.mem_Iic.mpr hz)

private theorem anchor_of_zero_run (Γ : Finset (Fin m)) (z : Fin m)
    (hm : 0<m) (h : TailSameRun Γ z ⟨0,hm⟩) (h0 : (⟨0,hm⟩ : Fin m)∈Γ) :
    AnchorSameRun Γ z := by
  intro g hg
  by_cases he : g=(⟨0,hm⟩ : Fin m)
  · exact he.symm ▸ h0
  · have hpos : (⟨0,hm⟩ : Fin m)<g := by
      change 0<g.val
      apply Nat.pos_of_ne_zero
      intro hz
      exact he (Fin.ext hz)
    apply h
    apply Finset.mem_Ioc.mpr
    rw [min_eq_right (show (⟨0,hm⟩ : Fin m)≤z from Nat.zero_le z.val),
      max_eq_left (show (⟨0,hm⟩ : Fin m)≤z from Nat.zero_le z.val)]
    exact ⟨hpos,Finset.mem_Iic.mp hg⟩

/-- The actual anchored Γ-run includes the original collapsed anchor weight. -/
theorem run_sum_of_anchor (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (Γ : Finset (Fin m)) (hzero : (∑ x,w x)=0)
    (hcuts : ∀ g∉Γ,prefixCoeff p w g.val=0) (z : Fin m)
    (ha : AnchorSameRun Γ z) :
    w none+(∑ k in runPositions Γ z,w (some (p.1 k)))=0 := by
  have hm : 0<m := lt_of_le_of_lt (Nat.zero_le z.val) z.isLt
  have hb := run_sum_boundary p w Γ hzero hcuts z
  change (∑ k in runPositions Γ z,w (some (p.1 k))) =
    -(if TailSameRun Γ z ⟨0,hm⟩ then w none else 0) at hb
  rw [if_pos (anchor_implies_zero_run Γ z hm ha)] at hb
  linarith only [hb]

/-- Every actual nonanchored Γ-run has zero total tail weight. -/
theorem run_sum_of_not_anchor (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (Γ : Finset (Fin m)) (hzero : (∑ x,w x)=0)
    (hcuts : ∀ g∉Γ,prefixCoeff p w g.val=0) (z : Fin m)
    (ha : ¬AnchorSameRun Γ z) :
    (∑ k in runPositions Γ z,w (some (p.1 k)))=0 := by
  classical
  have hm : 0<m := lt_of_le_of_lt (Nat.zero_le z.val) z.isLt
  have hb := run_sum_boundary p w Γ hzero hcuts z
  change (∑ k in runPositions Γ z,w (some (p.1 k))) =
    -(if TailSameRun Γ z ⟨0,hm⟩ then w none else 0) at hb
  by_cases hr : TailSameRun Γ z ⟨0,hm⟩
  · have h0 : (⟨0,hm⟩ : Fin m)∉Γ := fun h0 => ha (anchor_of_zero_run Γ z hm hr h0)
    have hz := hcuts ⟨0,hm⟩ h0
    have hw : w none=0 := by simpa [prefixCoeff] using hz
    simpa only [if_pos hr,hw,neg_zero] using hb
  · simpa only [if_neg hr,neg_zero] using hb

/-- A nonzero tail weight has another nonzero weight in its actual Γ-run,
or shares the anchor run with a nonzero collapsed anchor weight. -/
theorem nonzero_tail_has_run_partner (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (Γ : Finset (Fin m)) (hzero : (∑ x,w x)=0)
    (hcuts : ∀ g∉Γ,prefixCoeff p w g.val=0) (z : Fin m)
    (hz : w (some (p.1 z))≠0) :
    (∃ k,k≠z ∧ TailSameRun Γ z k ∧ w (some (p.1 k))≠0) ∨
      (AnchorSameRun Γ z ∧ w none≠0) := by
  classical
  by_cases hp : ∃ k,k≠z ∧ TailSameRun Γ z k ∧ w (some (p.1 k))≠0
  · exact Or.inl hp
  right
  have hsum : (∑ k in runPositions Γ z,w (some (p.1 k)))=w (some (p.1 z)) := by
    apply Finset.sum_eq_single z
    · intro k hk hkz
      by_contra hkn
      exact hp ⟨k,hkz,(mem_runPositions Γ z k).mp hk,hkn⟩
    · intro hn
      exact (hn ((mem_runPositions Γ z z).mpr (tailSameRun_refl Γ z))).elim
  have ha : AnchorSameRun Γ z := by
    by_contra ha
    have he := run_sum_of_not_anchor p w Γ hzero hcuts z ha
    rw [hsum] at he
    exact hz he
  refine ⟨ha,?_⟩
  intro hn
  have he := run_sum_of_anchor p w Γ hzero hcuts z ha
  rw [hn,hsum,zero_add] at he
  exact hz he

#print axioms run_sum_of_anchor
#print axioms run_sum_of_not_anchor
#print axioms nonzero_tail_has_run_partner
end MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
