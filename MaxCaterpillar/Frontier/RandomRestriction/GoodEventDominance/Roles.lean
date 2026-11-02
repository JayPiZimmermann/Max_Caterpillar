import MaxCaterpillar.Frontier.RandomRestriction.GoodEventMembership

/-! # Actual support witnesses enter the counted bad event

The role spaces retain unordered cherry pairs, and in cases A/C an unordered
second pair. Their actual embeddings may enumerate either pair in either order.
Symmetry of the placement geometry, rather than an ordering assumption, makes
four explicit supported labels witnesses for the counted event.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
open GoodEvent
variable {m : ℕ}

private theorem pair_relation {α : Type*} (R : α → α → Prop)
    (hs : ∀ x y,R x y → R y x) {a b x y : α} (hab : R a b)
    (hxy : x≠y) (hx : x=a ∨ x=b) (hy : y=a ∨ y=b) : R x y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact False.elim (hxy (hx.trans hy.symm))
  · rw [hx,hy]
    exact hab
  · rw [hx,hy]
    exact hs a b hab
  · exact False.elim (hxy (hx.trans hy.symm))

private theorem adjacent_symm (Γ : Finset (Fin m)) (a b : Fin m)
    (h : TailAdjacent Γ a b) : TailAdjacent Γ b a := Or.symm h
private theorem sameRun_symm (Γ : Finset (Fin m)) (a b : Fin m)
    (h : TailSameRun Γ a b) : TailSameRun Γ b a := by
  change tailInterval b a ⊆ Γ
  rwa [tailInterval_comm]

private theorem tail_ne_selected (a : Fin m) (s : Fin 5) :
    tailPosition m a ≠ selectedPosition m s := by
  intro he
  have hv := congrArg Fin.val he
  change a.val+5=s.val at hv
  have ht : 5≤a.val+5 := Nat.le_add_left 5 a.val
  rw [hv] at ht
  exact (not_lt_of_ge ht) s.isLt

private theorem original_tail_ne (τ : Equiv.Perm (Fin (m+5)))
    {a b : Fin m} (hab : a≠b) :
    τ.symm (tailPosition m a) ≠ τ.symm (tailPosition m b) := by
  intro he
  exact hab ((tailPosition m).injective (τ.symm.injective he))
private theorem original_selected_ne (τ : Equiv.Perm (Fin (m+5)))
    {s t : Fin 5} (hst : s≠t) :
    τ.symm (selectedPosition m s) ≠ τ.symm (selectedPosition m t) := by
  intro he
  exact hst ((selectedPosition m).injective (τ.symm.injective he))
private theorem original_tail_selected_ne (τ : Equiv.Perm (Fin (m+5)))
    (a : Fin m) (s : Fin 5) :
    τ.symm (tailPosition m a) ≠ τ.symm (selectedPosition m s) := by
  intro he
  exact tail_ne_selected a s (τ.symm.injective he)

private theorem exists_acRole {α : Type*} [DecidableEq α] (T : Finset α)
    (x y z w : α) (hxy : x≠y) (hxz : x≠z) (hxw : x≠w)
    (hyz : y≠z) (hyw : y≠w) (hzw : z≠w)
    (hx : x∈T) (hy : y∈T) (hz : z∈T) (hw : w∈T) :
    ∃ R : ACRole T,R.cherry={x,y} ∧ R.other={z,w} := by
  let P : PairRole T := ⟨{x,y},Finset.mem_powersetCard.mpr
    ⟨by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hx,hy⟩,
      by simp [hxy]⟩⟩
  have hzP : z∈T\P.val := by
    apply Finset.mem_sdiff.mpr
    exact ⟨hz,by simp [P,Ne.symm hxz,Ne.symm hyz]⟩
  have hwP : w∈T\P.val := by
    apply Finset.mem_sdiff.mpr
    exact ⟨hw,by simp [P,Ne.symm hxw,Ne.symm hyw]⟩
  let Q : PairRole (T\P.val) := ⟨{z,w},Finset.mem_powersetCard.mpr
    ⟨by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hzP,hwP⟩,
      by simp [hzw]⟩⟩
  exact ⟨⟨P,Q⟩,rfl,rfl⟩

private theorem exists_bRole {α : Type*} [DecidableEq α] (T : Finset α)
    (x y z w : α) (hxy : x≠y) (hxz : x≠z) (hxw : x≠w)
    (hyz : y≠z) (hyw : y≠w) (hzw : z≠w)
    (hx : x∈T) (hy : y∈T) (hz : z∈T) (hw : w∈T) :
    ∃ R : BRole T,R.cherry={x,y} ∧ R.tail=z ∧ R.selected=w := by
  let P : PairRole T := ⟨{x,y},Finset.mem_powersetCard.mpr
    ⟨by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hx,hy⟩,
      by simp [hxy]⟩⟩
  have hzP : z∈T\P.val := by
    apply Finset.mem_sdiff.mpr
    exact ⟨hz,by simp [P,Ne.symm hxz,Ne.symm hyz]⟩
  have hwP : w∈(T\P.val).erase z := by
    apply Finset.mem_erase.mpr
    exact ⟨hzw.symm,Finset.mem_sdiff.mpr
      ⟨hw,by simp [P,Ne.symm hxw,Ne.symm hyw]⟩⟩
  exact ⟨⟨P,⟨⟨z,hzP⟩,⟨w,hwP⟩⟩⟩,rfl,rfl,rfl⟩

private theorem original_pair_positions (τ : Equiv.Perm (Fin (m+5)))
    (x y z : Fin (m+5)) (hz : z∈({τ.symm x,τ.symm y} : Finset (Fin (m+5)))) :
    τ z=x ∨ τ z=y := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact Or.inl (τ.apply_symm_apply x)
  · exact Or.inr (τ.apply_symm_apply y)

private theorem tail_bound {a : Fin m} {p : Fin (m+5)}
    (h : p=tailPosition m a) : 5≤p.val := by
  rw [h,tailPosition_val]
  exact Nat.le_add_left 5 a.val
private theorem tail_pair_bound {a b : Fin m} {p : Fin (m+5)}
    (h : p=tailPosition m a ∨ p=tailPosition m b) : 5≤p.val :=
  h.elim tail_bound tail_bound
private theorem selected_pair_bound {s t : Fin 5} {p : Fin (m+5)}
    (h : p=selectedPosition m s ∨ p=selectedPosition m t) : p.val<5 := by
  rcases h with h | h
  · rw [h,selectedPosition_val]
    exact s.isLt
  · rw [h,selectedPosition_val]
    exact t.isLt

private theorem decode_eq {n : ℕ} (q : Fin n ↪ Fin (m+5))
    (ht : ∀ i,5≤(q i).val) (i : Fin n) (a : Fin m)
    (h : q i=tailPosition m a) : tailDecode q ht i=a :=
  (tailPosition m).injective ((tailDecode_reconstruct q ht i).trans h)
private theorem decode_pair {n : ℕ} (q : Fin n ↪ Fin (m+5))
    (ht : ∀ i,5≤(q i).val) (i : Fin n) (a b : Fin m)
    (h : q i=tailPosition m a ∨ q i=tailPosition m b) :
    tailDecode q ht i=a ∨ tailDecode q ht i=b :=
  h.elim (fun he => Or.inl (decode_eq q ht i a he))
    (fun he => Or.inr (decode_eq q ht i b he))

private theorem fullA (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5))
    (a b c d : Fin m)
    (h0 : q 0=tailPosition m a ∨ q 0=tailPosition m b)
    (h1 : q 1=tailPosition m a ∨ q 1=tailPosition m b)
    (h2 : q 2=tailPosition m c ∨ q 2=tailPosition m d)
    (h3 : q 3=tailPosition m c ∨ q 3=tailPosition m d)
    (ha : TailAdjacent Γ a b) (hr : TailSameRun Γ c d) : q∈fullCaseA Γ := by
  classical
  have ht : ∀ i,5≤(q i).val := by
    intro i
    fin_cases i
    · exact tail_pair_bound h0
    · exact tail_pair_bound h1
    · exact tail_pair_bound h2
    · exact tail_pair_bound h3
  apply mem_fullCaseA_of_tail Γ q ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,?_⟩
  · exact pair_relation (TailAdjacent Γ) (adjacent_symm Γ) ha
      (fun he => (by decide : (0 : Fin 4)≠1) ((tailDecode q ht).injective he))
      (decode_pair q ht 0 a b h0) (decode_pair q ht 1 a b h1)
  · exact pair_relation (TailSameRun Γ) (sameRun_symm Γ) hr
      (fun he => (by decide : (2 : Fin 4)≠3) ((tailDecode q ht).injective he))
      (decode_pair q ht 2 c d h2) (decode_pair q ht 3 c d h3)

private theorem fullB (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5))
    (a b z : Fin m) (s : Fin 5)
    (h0 : q 0=tailPosition m a ∨ q 0=tailPosition m b)
    (h1 : q 1=tailPosition m a ∨ q 1=tailPosition m b)
    (h2 : q 2=tailPosition m z) (h3 : q 3=selectedPosition m s)
    (ha : TailAdjacent Γ a b) (hr : AnchorSameRun Γ z) : q∈fullCaseB Γ := by
  classical
  have ht : ∀ i,5≤(firstThree q i).val := by
    intro i
    fin_cases i
    · exact tail_pair_bound h0
    · exact tail_pair_bound h1
    · exact tail_bound h2
  have hs : (q 3).val<5 := by rw [h3,selectedPosition_val]; exact s.isLt
  apply mem_fullCaseB_of_tail Γ q ht hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,?_⟩
  · exact pair_relation (TailAdjacent Γ) (adjacent_symm Γ) ha
      (fun he => (by decide : (0 : Fin 3)≠1) ((tailDecode (firstThree q) ht).injective he))
      (decode_pair (firstThree q) ht 0 a b h0) (decode_pair (firstThree q) ht 1 a b h1)
  · have he := decode_eq (firstThree q) ht 2 z h2
    rw [he]
    exact hr

private theorem fullC (Γ : Finset (Fin m)) (q : Fin 4 ↪ Fin (m+5))
    (a b : Fin m) (s t : Fin 5)
    (h0 : q 0=tailPosition m a ∨ q 0=tailPosition m b)
    (h1 : q 1=tailPosition m a ∨ q 1=tailPosition m b)
    (h2 : q 2=selectedPosition m s ∨ q 2=selectedPosition m t)
    (h3 : q 3=selectedPosition m s ∨ q 3=selectedPosition m t)
    (ha : TailAdjacent Γ a b) : q∈fullCaseC Γ := by
  classical
  have ht : ∀ i,5≤(firstTwo q i).val := by
    intro i
    fin_cases i
    · exact tail_pair_bound h0
    · exact tail_pair_bound h1
  have hs : ∀ i,(lastTwo q i).val<5 := by
    intro i
    fin_cases i
    · exact selected_pair_bound h2
    · exact selected_pair_bound h3
  apply mem_fullCaseC_of_tail Γ q ht hs
  exact pair_relation (TailAdjacent Γ) (adjacent_symm Γ) ha
    (fun he => (by decide : (0 : Fin 2)≠1) ((tailDecode (firstTwo q) ht).injective he))
    (decode_pair (firstTwo q) ht 0 a b h0) (decode_pair (firstTwo q) ht 1 a b h1)

/-- Four distinct supported tail labels with A geometry enter the actual event,
independently of how either unordered support pair was enumerated. -/
theorem caseA_mem_supportBadAt (T : Finset (Fin (m+5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m+5))) (a b c d : Fin m)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : τ.symm (tailPosition m a)∈T) (hb : τ.symm (tailPosition m b)∈T)
    (hc : τ.symm (tailPosition m c)∈T) (hd : τ.symm (tailPosition m d)∈T)
    (hAdj : TailAdjacent Γ a b) (hRun : TailSameRun Γ c d) :
    τ∈supportBadAt T Γ := by
  classical
  obtain ⟨R,hR,hO⟩ := exists_acRole T _ _ _ _
    (original_tail_ne τ hab) (original_tail_ne τ hac) (original_tail_ne τ had)
    (original_tail_ne τ hbc) (original_tail_ne τ hbd) (original_tail_ne τ hcd) ha hb hc hd
  apply mem_supportBadAt_of_caseA T Γ τ R
  apply fullA Γ (UniformTuples.induced R.embedding τ) a b c d
  · apply original_pair_positions τ
    rw [ACRole.embedding_zero]
    rw [← hR]
    exact pairEmbedding_mem _ _ 0
  · apply original_pair_positions τ
    rw [ACRole.embedding_one]
    rw [← hR]
    exact pairEmbedding_mem _ _ 1
  · apply original_pair_positions τ
    rw [ACRole.embedding_two]
    rw [← hO]
    exact pairEmbedding_mem _ _ 0
  · apply original_pair_positions τ
    rw [ACRole.embedding_three]
    rw [← hO]
    exact pairEmbedding_mem _ _ 1
  · exact hAdj
  · exact hRun

/-- Three distinct supported tails and one supported selected label with B
geometry enter the actual event, with an unordered cherry and ordered remainder. -/
theorem caseB_mem_supportBadAt (T : Finset (Fin (m+5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m+5))) (a b z : Fin m) (s : Fin 5)
    (hab : a≠b) (haz : a≠z) (hbz : b≠z)
    (ha : τ.symm (tailPosition m a)∈T) (hb : τ.symm (tailPosition m b)∈T)
    (hz : τ.symm (tailPosition m z)∈T) (hs : τ.symm (selectedPosition m s)∈T)
    (hAdj : TailAdjacent Γ a b) (hRun : AnchorSameRun Γ z) :
    τ∈supportBadAt T Γ := by
  classical
  obtain ⟨R,hR,hZ,hS⟩ := exists_bRole T _ _ _ _
    (original_tail_ne τ hab) (original_tail_ne τ haz) (original_tail_selected_ne τ a s)
    (original_tail_ne τ hbz) (original_tail_selected_ne τ b s)
    (original_tail_selected_ne τ z s) ha hb hz hs
  apply mem_supportBadAt_of_caseB T Γ τ R
  apply fullB Γ (UniformTuples.induced R.embedding τ) a b z s
  · apply original_pair_positions τ
    rw [BRole.embedding_zero]
    rw [← hR]
    exact pairEmbedding_mem _ _ 0
  · apply original_pair_positions τ
    rw [BRole.embedding_one]
    rw [← hR]
    exact pairEmbedding_mem _ _ 1
  · change τ R.tail=tailPosition m z
    rw [hZ,τ.apply_symm_apply]
  · change τ R.selected=selectedPosition m s
    rw [hS,τ.apply_symm_apply]
  · exact hAdj
  · exact hRun

/-- Two distinct supported tails and two distinct supported selected labels
with C geometry enter the actual event without ordering either pair. -/
theorem caseC_mem_supportBadAt (T : Finset (Fin (m+5))) (Γ : Finset (Fin m))
    (τ : Equiv.Perm (Fin (m+5))) (a b : Fin m) (s t : Fin 5)
    (hab : a≠b) (hst : s≠t)
    (ha : τ.symm (tailPosition m a)∈T) (hb : τ.symm (tailPosition m b)∈T)
    (hs : τ.symm (selectedPosition m s)∈T) (ht : τ.symm (selectedPosition m t)∈T)
    (hAdj : TailAdjacent Γ a b) : τ∈supportBadAt T Γ := by
  classical
  obtain ⟨R,hR,hO⟩ := exists_acRole T _ _ _ _
    (original_tail_ne τ hab) (original_tail_selected_ne τ a s)
    (original_tail_selected_ne τ a t) (original_tail_selected_ne τ b s)
    (original_tail_selected_ne τ b t) (original_selected_ne τ hst) ha hb hs ht
  apply mem_supportBadAt_of_caseC T Γ τ R
  apply fullC Γ (UniformTuples.induced R.embedding τ) a b s t
  · apply original_pair_positions τ
    rw [ACRole.embedding_zero]
    rw [← hR]
    exact pairEmbedding_mem _ _ 0
  · apply original_pair_positions τ
    rw [ACRole.embedding_one]
    rw [← hR]
    exact pairEmbedding_mem _ _ 1
  · apply original_pair_positions τ
    rw [ACRole.embedding_two]
    rw [← hO]
    exact pairEmbedding_mem _ _ 0
  · apply original_pair_positions τ
    rw [ACRole.embedding_three]
    rw [← hO]
    exact pairEmbedding_mem _ _ 1
  · exact hAdj

end MaxCaterpillar.Frontier.RandomRestriction.GoodEventDominance
