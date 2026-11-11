import MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance.Runs
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesDefs
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Realization

/-! # Actual prefix cuts and an isolated low-rank pair

The pair weights and its run are consequences of the original rank/prefix
conditions. Neither pair cancellation nor run separation is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
open BigOperators GoodEvent Cartesian DominantGap
variable {m : ℕ}

/-- A dominant nonzero prefix below K forces every cut outside the actual
low-rank set to vanish. -/
theorem dominant_prefix_cuts_zero (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (hzero : (∑ x,w x)=0) (K : ℕ) (g : Fin m)
    (hd : GapDominant p w g) (hg : (p.2 g).val<K) :
    ∀ k∉smallRankGaps p.2 K,prefixCoeff p w k.val=0 := by
  intro k hk
  rw [← tailCoefficient_eq_prefixCoeff p w hzero k]
  by_contra hn
  have hkg : k≠g := by
    intro he
    subst k
    exact hk ((mem_smallRankGaps p.2 g).mpr hg)
  have hlt := hd.2 k hn hkg
  exact hk ((mem_smallRankGaps p.2 k).mpr (lt_trans hlt hg))

/-- The two actual tail weights at an isolated gap are opposite, and are
exactly the nonzero central prefix with its sign reversed. -/
theorem isolated_pair_prefix_values (p : RawConfig m) (w : Option (Fin m)→ℝ)
    (Γ : Finset (Fin m)) (hzero : (∑ x,w x)=0)
    (hcuts : ∀ k∉Γ,prefixCoeff p w k.val=0)
    (g : Fin m) (hg : g∈isolatedGaps Γ) :
    w (some (p.1 (isolatedGapPredecessor g)))=prefixCoeff p w g.val ∧
      w (some (p.1 g)) = -prefixCoeff p w g.val := by
  have hgi := (mem_isolatedGaps g Γ).mp hg
  have hsucc := isolatedGapPredecessor_succ g hgi.2.1
  have ha : isolatedGapPredecessor g∉Γ := by
    intro ha
    exact (hgi.2.2 _ ha).1 hsucc
  have hleft := hcuts (isolatedGapPredecessor g) ha
  have hright : prefixCoeff p w (g.val+1)=0 := by
    by_cases hb : g.val+1<m
    · let b : Fin m := ⟨g.val+1,hb⟩
      have hbΓ : b∉Γ := by
        intro hh
        exact (hgi.2.2 b hh).2 rfl
      exact hcuts b hbΓ
    · have he : g.val+1=m :=
        Nat.le_antisymm (Nat.succ_le_of_lt g.isLt) (le_of_not_gt hb)
      rw [he,prefixCoeff_at_card,hzero]
  have hL := prefixCoeff_succ p w (isolatedGapPredecessor g)
  rw [hsucc] at hL
  have hR := prefixCoeff_succ p w g
  constructor <;> linarith only [hleft,hright,hL,hR]

lemma isolated_pair_adjacent (Γ : Finset (Fin m)) (g : Fin m)
    (hg : g∈isolatedGaps Γ) : TailAdjacent Γ (isolatedGapPredecessor g) g :=
  Or.inl ⟨isolatedGapPredecessor_succ g ((mem_isolatedGaps g Γ).mp hg).2.1,
    ((mem_isolatedGaps g Γ).mp hg).1⟩

lemma isolated_pair_sameRun (Γ : Finset (Fin m)) (g : Fin m)
    (hg : g∈isolatedGaps Γ) : TailSameRun Γ (isolatedGapPredecessor g) g := by
  have hgi := (mem_isolatedGaps g Γ).mp hg
  have hsucc := isolatedGapPredecessor_succ g hgi.2.1
  have hle : isolatedGapPredecessor g≤g := by change _≤g.val; linarith only [hsucc]
  intro k hk
  have hh : isolatedGapPredecessor g<k ∧ k≤g := by
    simpa only [tailInterval,min_eq_left hle,max_eq_right hle,Finset.mem_Ioc] using hk
  have he : k=g := by
    apply Fin.ext
    have hlo : (isolatedGapPredecessor g).val<k.val := hh.1
    have hup : k.val≤g.val := hh.2
    linarith only [hlo,hup,hsucc]
  exact he ▸ hgi.1

/-- The entire run of an isolated tail pair consists of its two endpoints. -/
theorem isolated_pair_run_members (Γ : Finset (Fin m)) (g : Fin m)
    (hg : g∈isolatedGaps Γ) (z : Fin m)
    (hrun : TailSameRun Γ (isolatedGapPredecessor g) z) :
    z=isolatedGapPredecessor g ∨ z=g := by
  classical
  have hgi := (mem_isolatedGaps g Γ).mp hg
  have hsucc := isolatedGapPredecessor_succ g hgi.2.1
  by_cases hza : z=isolatedGapPredecessor g
  · exact Or.inl hza
  by_cases hzg : z=g
  · exact Or.inr hzg
  have hne : z.val≠(isolatedGapPredecessor g).val := fun he => hza (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hz | hz
  · have hz' : z<isolatedGapPredecessor g := hz
    have hm : isolatedGapPredecessor g∈tailInterval (isolatedGapPredecessor g) z := by
      simp only [tailInterval,min_eq_right hz'.le,max_eq_left hz'.le,Finset.mem_Ioc]
      exact ⟨hz',le_rfl⟩
    exact ((hgi.2.2 _ (hrun hm)).1 hsucc).elim
  · have hglt : g.val<z.val := by
      rcases lt_trichotomy z.val g.val with h | h | h
      · linarith only [hz,h,hsucc]
      · exact (hzg (Fin.ext h)).elim
      · exact h
    let b : Fin m := ⟨g.val+1,lt_of_le_of_lt (Nat.succ_le_of_lt hglt) z.isLt⟩
    have hle : isolatedGapPredecessor g≤z := by change _≤z.val; linarith only [hz]
    have hm : b∈tailInterval (isolatedGapPredecessor g) z := by
      simp only [tailInterval,min_eq_left hle,max_eq_right hle,Finset.mem_Ioc]
      constructor
      · change (isolatedGapPredecessor g).val<g.val+1
        linarith only [hsucc]
      · exact Nat.succ_le_of_lt hglt
    exact ((hgi.2.2 b (hrun hm)).2 rfl).elim

/-- A different run cannot return a partner inside the isolated pair. -/
theorem run_partner_outside_isolated (Γ : Finset (Fin m)) (g : Fin m)
    (hg : g∈isolatedGaps Γ) (z k : Fin m)
    (hz : z≠isolatedGapPredecessor g) (hzg : z≠g)
    (hzk : TailSameRun Γ z k) : k≠isolatedGapPredecessor g ∧ k≠g := by
  constructor
  · intro he
    rw [he] at hzk
    exact (isolated_pair_run_members Γ g hg z (tailSameRun_symm Γ hzk)).elim hz hzg
  · intro he
    rw [he] at hzk
    have h := tailSameRun_trans Γ (isolated_pair_sameRun Γ g hg) (tailSameRun_symm Γ hzk)
    exact (isolated_pair_run_members Γ g hg z h).elim hz hzg

#print axioms dominant_prefix_cuts_zero
#print axioms isolated_pair_prefix_values
#print axioms isolated_pair_run_members
end MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
