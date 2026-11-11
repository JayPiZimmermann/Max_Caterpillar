import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability

/-! A finite second-moment bound for selected adjacent gaps. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Overnight.Constants.Cherry
open BigOperators Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}
attribute [local instance] Classical.propDecidable

def vertices (e : Fin m × Fin m) : Finset (Fin m) := {e.1,e.2}

def near (e f : Fin m × Fin m) : Prop :=
  e.1.val ≤ f.1.val+1 ∧ f.1.val ≤ e.1.val+1

lemma edge_first_injective (e f : Fin m × Fin m)
    (he : e∈allGapAdjacencies) (hf : f∈allGapAdjacencies)
    (h : e.1.val=f.1.val) : e=f := by
  apply Prod.ext (Fin.ext h)
  apply Fin.ext
  have he' := (mem_allGapAdjacencies e.1 e.2).mp he
  have hf' := (mem_allGapAdjacencies f.1 f.2).mp hf
  linarith

lemma near_card_le (e : Fin m × Fin m) :
    (allGapAdjacencies.filter (near e)).card ≤ 3 := by
  classical
  let S := allGapAdjacencies.filter (near e)
  have hi : Set.InjOn (fun f : Fin m × Fin m => f.1.val) S := by
    intro f hf g hg hfg
    exact edge_first_injective f g (Finset.mem_filter.mp hf).1
      (Finset.mem_filter.mp hg).1 hfg
  have hs : S.image (fun f : Fin m × Fin m => f.1.val) ⊆
      Finset.Icc (e.1.val-1) (e.1.val+1) := by
    intro z hz
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hz
    have hn := (Finset.mem_filter.mp hf).2
    change e.1.val≤f.1.val+1 ∧ f.1.val≤e.1.val+1 at hn
    exact Finset.mem_Icc.mpr ⟨Nat.sub_le_of_le_add hn.1,hn.2⟩
  calc
    S.card = (S.image (fun f : Fin m × Fin m => f.1.val)).card :=
      (Finset.card_image_of_injOn hi).symm
    _ ≤ (Finset.Icc (e.1.val-1) (e.1.val+1)).card := Finset.card_le_of_subset hs
    _ ≤ 3 := by
      rw [Nat.card_Icc]
      by_cases hz : e.1.val=0
      · norm_num [hz]
      · have hp : 1≤e.1.val := Nat.one_le_iff_ne_zero.mpr hz
        have hh := Nat.sub_add_cancel hp
        apply Nat.sub_le_of_le_add
        linarith

lemma vertices_card (e : Fin m × Fin m) (he : e∈allGapAdjacencies) :
    (vertices e).card=2 := by
  have h := (mem_allGapAdjacencies e.1 e.2).mp he
  have hn : e.1≠e.2 := by intro heq; have hv := congrArg Fin.val heq; linarith
  simp [vertices,hn]

lemma union_vertices_card_near (e f : Fin m × Fin m)
    (he : e∈allGapAdjacencies) (hf : f∈allGapAdjacencies)
    (hne : e≠f) (hn : near e f) : (vertices e ∪ vertices f).card=3 := by
  have he' := (mem_allGapAdjacencies e.1 e.2).mp he
  have hf' := (mem_allGapAdjacencies f.1 f.2).mp hf
  have hfirst : e.1.val≠f.1.val := fun h => hne (edge_first_injective e f he hf h)
  have he12 : e.1≠e.2 := by intro h; have := congrArg Fin.val h; linarith
  have hf12 : f.1≠f.2 := by intro h; have := congrArg Fin.val h; linarith
  have h11 : e.1≠f.1 := by intro h; exact hfirst (congrArg Fin.val h)
  change e.1.val≤f.1.val+1 ∧ f.1.val≤e.1.val+1 at hn
  rcases lt_or_gt_of_ne hfirst with hlt | hgt
  · have hcross : e.2=f.1 := Fin.ext (by linarith)
    have h14 : e.1≠f.2 := by intro h; have := congrArg Fin.val h; linarith
    have hu : vertices e ∪ vertices f = {e.1,f.1,f.2} := by
      ext z
      simp only [vertices,hcross,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      tauto
    rw [hu]
    simp [h11,h14,hf12]
  · have hcross : f.2=e.1 := Fin.ext (by linarith)
    have h32 : f.1≠e.2 := by intro h; have := congrArg Fin.val h; linarith
    have hu : vertices e ∪ vertices f = {f.1,e.1,e.2} := by
      ext z
      simp only [vertices,hcross,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      tauto
    rw [hu]
    simp [he12,h11,h32,Ne.symm h11]

lemma union_vertices_card_far (e f : Fin m × Fin m)
    (he : e∈allGapAdjacencies) (hf : f∈allGapAdjacencies)
    (hn : ¬near e f) : (vertices e ∪ vertices f).card=4 := by
  have he' := (mem_allGapAdjacencies e.1 e.2).mp he
  have hf' := (mem_allGapAdjacencies f.1 f.2).mp hf
  have hne (a b : Fin m) (ha : a∈vertices e) (hb : b∈vertices f) : a≠b := by
    simp only [vertices,Finset.mem_insert,Finset.mem_singleton] at ha hb
    intro h
    have hv := congrArg Fin.val h
    apply hn
    change e.1.val≤f.1.val+1 ∧ f.1.val≤e.1.val+1
    rcases ha with ha|ha <;> rcases hb with hb|hb <;>
      have hva := congrArg Fin.val ha <;> have hvb := congrArg Fin.val hb <;>
      constructor <;> linarith
  have hd : Disjoint (vertices e) (vertices f) :=
    Finset.disjoint_left.mpr (fun a ha hb => hne a a ha hb rfl)
  rw [Finset.card_union_eq hd, vertices_card e he,vertices_card f hf]

lemma weighted_square_eq {Ω : Type*} [Fintype Ω]
    (p : Ω→ℝ) (Γ : Ω→Finset (Fin m)) :
    (∑ ω,p ω*((selectedGapAdjacencies (Γ ω)).card:ℝ)^2) =
      ∑ e in allGapAdjacencies,∑ f in allGapAdjacencies,
        containmentWeight p Γ (vertices e ∪ vertices f) := by
  classical
  have hp (ω : Ω) : ((selectedGapAdjacencies (Γ ω)).card:ℝ)^2 =
      ∑ e in allGapAdjacencies,∑ f in allGapAdjacencies,
        if vertices e ∪ vertices f ⊆ Γ ω then (1:ℝ) else 0 := by
    simp only [selectedGapAdjacencies,Finset.natCast_card_filter,pow_two]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    simp only [vertices,Finset.union_subset_iff,Finset.insert_subset_iff,
      Finset.singleton_subset_iff]
    split_ifs <;> norm_num <;> tauto
  simp_rw [hp,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  rfl

/-- Pair collisions contribute only a linear number of exceptional terms. -/
theorem rankAverage_adjacency_square_le (hm : 0<m) (hKm : K≤m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((selectedGapAdjacencies Γ).card:ℝ)^2) ≤
      (K:ℝ)^4/(m:ℝ)^2 + 3*(K:ℝ)^3/(m:ℝ)^2 + (K:ℝ)^2/(m:ℝ) := by
  classical
  let p : ℝ := (K:ℝ)/(m:ℝ)
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have hp0 : 0≤p := by dsimp [p]; positivity
  let w : Finset (Fin m)→ℝ := containmentWeight
    (fun _ : Equiv.Perm (Fin m) => 1/(Fintype.card (Equiv.Perm (Fin m)):ℝ))
    (fun ρ => smallRankGaps ρ K)
  have hpair (e f : Fin m × Fin m) (he : e∈allGapAdjacencies)
      (hf : f∈allGapAdjacencies) :
      w (vertices e ∪ vertices f) ≤ p^4 + (if near e f then p^3 else 0) +
        (if e=f then p^2 else 0) := by
    have hw := rank_containment_weight_le hm hKm (vertices e ∪ vertices f)
    change w (vertices e ∪ vertices f) ≤ p^(vertices e ∪ vertices f).card at hw
    by_cases hef : e=f
    · subst f
      rw [Finset.union_self,vertices_card e he] at hw
      rw [if_pos (rfl : e=e),Finset.union_self]
      have ht : 0≤(if near e e then p^3 else 0) := by positivity
      nlinarith only [hw,pow_nonneg hp0 4,ht]
    · rw [if_neg hef]
      by_cases hn : near e f
      · rw [if_pos hn]
        rw [union_vertices_card_near e f he hf hef hn] at hw
        linarith only [hw,pow_nonneg hp0 4]
      · rw [if_neg hn]
        rw [union_vertices_card_far e f he hf hn] at hw
        simpa using hw
  have hinner (e : Fin m × Fin m) (he : e∈allGapAdjacencies) :
      (∑ f in allGapAdjacencies,w (vertices e ∪ vertices f)) ≤
        (m:ℝ)*p^4+3*p^3+p^2 := by
    have hs := Finset.sum_le_sum (fun f hf => hpair e f he hf)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
    have hn : (∑ f in allGapAdjacencies,if near e f then p^3 else 0) ≤ 3*p^3 := by
      rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast near_card_le e) (pow_nonneg hp0 3)
    have hd : (∑ f in allGapAdjacencies,if e=f then p^2 else 0)=p^2 := by
      simp only [Finset.sum_ite_eq,if_pos he]
    have hcount : ((allGapAdjacencies (m:=m)).card:ℝ)≤m := by
      exact_mod_cast allGapAdjacencies_card_le (m:=m)
    have hc := mul_le_mul_of_nonneg_right hcount (pow_nonneg hp0 4)
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    rw [hd] at hs
    linarith only [hs,hn,hc]
  unfold rankAverage
  rw [weighted_square_eq]
  change (∑ e in allGapAdjacencies,∑ f in allGapAdjacencies,w (vertices e ∪ vertices f)) ≤ _
  calc
    _ ≤ ∑ _e in allGapAdjacencies (m:=m), ((m:ℝ)*p^4+3*p^3+p^2) :=
      Finset.sum_le_sum hinner
    _ ≤ (m:ℝ)*((m:ℝ)*p^4+3*p^3+p^2) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast allGapAdjacencies_card_le (m:=m)
      · positivity
    _ = _ := by dsimp [p]; field_simp [hm0.ne']; ring

#print axioms rankAverage_adjacency_square_le
end MaxCaterpillar.Overnight.Constants.Cherry
