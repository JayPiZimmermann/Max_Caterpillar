import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.UniformPlacement
import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesRoles
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset

/-! # Intrinsic original-label support bad events

The selected set and its literal complement enumeration are the actual sample.
A tail permutation sends tail positions to complement-enumeration indices.
Every support role consists of four fixed original labels, independently of
selection. Event membership records their actual placements and gap geometry;
no probability estimate is part of these definitions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {n : ℕ}

def firstThreeLabels (q : Fin 4 ↪ Fin n) : Fin 3 ↪ Fin n :=
  Fin.castSuccEmb.toEmbedding.trans q
def firstTwoLabels (q : Fin 4 ↪ Fin n) : Fin 2 ↪ Fin n :=
  (Fin.castAddEmb 2).toEmbedding.trans q
@[simp] lemma firstThreeLabels_apply (q : Fin 4 ↪ Fin n) (i : Fin 3) :
    firstThreeLabels q i=q i.castSucc := rfl
@[simp] lemma firstTwoLabels_apply (q : Fin 4 ↪ Fin n) (i : Fin 2) :
    firstTwoLabels q i=q (Fin.castAdd 2 i) := rfl

noncomputable def caseCTailPlacements {m : ℕ} (Γ : Finset (Fin m)) :
    Finset (Fin 2 ↪ Fin m) := by
  classical
  exact Finset.univ.filter fun q => TailAdjacent Γ (q 0) (q 1)
@[simp] lemma mem_caseCTailPlacements {m : ℕ} (Γ : Finset (Fin m)) (q : Fin 2 ↪ Fin m) :
    q∈caseCTailPlacements Γ ↔ TailAdjacent Γ (q 0) (q 1) := by
  classical
  simp only [caseCTailPlacements,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def caseA (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (R : ACRole T) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S))) :=
  placementEvent (Sampling.tail S) R.embedding (caseAPlacements Γ)
noncomputable def caseB (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (R : BRole T) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S))) := by
  classical
  exact if R.selected∈S then
    placementEvent (Sampling.tail S) (firstThreeLabels R.embedding) (caseBPlacements Γ) else ∅
noncomputable def caseC (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (R : ACRole T) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S))) := by
  classical
  exact if R.other⊆S then
    placementEvent (Sampling.tail S) (firstTwoLabels R.embedding) (caseCTailPlacements Γ) else ∅

@[simp] theorem mem_caseA (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (R : ACRole T)
    (τ : Equiv.Perm (Fin (Sampling.tailCount S))) :
    τ∈caseA T S Γ R ↔ ∃q∈caseAPlacements Γ,∀i,Sampling.tail S (τ (q i))=R.embedding i :=
  mem_placementEvent _ _ _ _
@[simp] theorem mem_caseB (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (R : BRole T)
    (τ : Equiv.Perm (Fin (Sampling.tailCount S))) :
    τ∈caseB T S Γ R ↔ R.selected∈S ∧
      ∃q∈caseBPlacements Γ,∀i,Sampling.tail S (τ (q i))=firstThreeLabels R.embedding i := by
  classical
  by_cases hs : R.selected∈S
  · simp only [caseB,if_pos hs,if_true,mem_placementEvent,hs,true_and]
  · simp only [caseB,if_neg hs,if_false,Finset.not_mem_empty,hs,false_and]
@[simp] theorem mem_caseC (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (R : ACRole T)
    (τ : Equiv.Perm (Fin (Sampling.tailCount S))) :
    τ∈caseC T S Γ R ↔ R.other⊆S ∧
      ∃q∈caseCTailPlacements Γ,∀i,Sampling.tail S (τ (q i))=firstTwoLabels R.embedding i := by
  classical
  by_cases hs : R.other⊆S
  · simp only [caseC,if_pos hs,if_true,mem_placementEvent,hs,true_and]
  · simp only [caseC,if_neg hs,if_false,Finset.not_mem_empty,hs,false_and]

/-- The original support roles are fixed before selecting S. -/
noncomputable def supportBadAt (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S))) := by
  classical
  exact ((Finset.univ.biUnion fun R : ACRole T => caseA T S Γ R) ∪
    (Finset.univ.biUnion fun R : BRole T => caseB T S Γ R)) ∪
    (Finset.univ.biUnion fun R : ACRole T => caseC T S Γ R)

theorem mem_supportBadAt (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S))) :
    τ∈supportBadAt T S Γ ↔
      (∃R : ACRole T,τ∈caseA T S Γ R) ∨ (∃R : BRole T,τ∈caseB T S Γ R) ∨
      (∃R : ACRole T,τ∈caseC T S Γ R) := by
  classical
  simp only [supportBadAt,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,or_assoc]
theorem mem_supportBadAt_of_caseA (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (R : ACRole T) (h : τ∈caseA T S Γ R) : τ∈supportBadAt T S Γ :=
  (mem_supportBadAt T S Γ τ).mpr (Or.inl ⟨R,h⟩)
theorem mem_supportBadAt_of_caseB (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (R : BRole T) (h : τ∈caseB T S Γ R) : τ∈supportBadAt T S Γ :=
  (mem_supportBadAt T S Γ τ).mpr (Or.inr (Or.inl ⟨R,h⟩))
theorem mem_supportBadAt_of_caseC (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (R : ACRole T) (h : τ∈caseC T S Γ R) : τ∈supportBadAt T S Γ :=
  (mem_supportBadAt T S Γ τ).mpr (Or.inr (Or.inr ⟨R,h⟩))

noncomputable def supportBadConfigurations (T S : Finset (Fin n)) (K : ℕ) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S)) × Equiv.Perm (Fin (Sampling.tailCount S))) := by
  classical
  exact Finset.univ.filter fun p => p.1∈supportBadAt T S (smallRankGaps p.2 K)
@[simp] theorem mem_supportBadConfigurations (T S : Finset (Fin n)) (K : ℕ)
    (p : Equiv.Perm (Fin (Sampling.tailCount S)) × Equiv.Perm (Fin (Sampling.tailCount S))) :
    p∈supportBadConfigurations T S K ↔ p.1∈supportBadAt T S (smallRankGaps p.2 K) := by
  classical
  simp only [supportBadConfigurations,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def familyBadAt {κ : Type*} [Fintype κ] (supports : κ→Finset (Fin n))
    (S : Finset (Fin n)) (Γ : Finset (Fin (Sampling.tailCount S))) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S))) := by
  classical
  exact Finset.univ.biUnion fun j => supportBadAt (supports j) S Γ
@[simp] theorem mem_familyBadAt {κ : Type*} [Fintype κ] (supports : κ→Finset (Fin n))
    (S : Finset (Fin n)) (Γ : Finset (Fin (Sampling.tailCount S)))
    (τ : Equiv.Perm (Fin (Sampling.tailCount S))) :
    τ∈familyBadAt supports S Γ ↔ ∃j,τ∈supportBadAt (supports j) S Γ := by
  classical
  simp only [familyBadAt,Finset.mem_biUnion,Finset.mem_univ,true_and]
noncomputable def familyBadConfigurations {κ : Type*} [Fintype κ] (supports : κ→Finset (Fin n))
    (S : Finset (Fin n)) (K : ℕ) :
    Finset (Equiv.Perm (Fin (Sampling.tailCount S)) × Equiv.Perm (Fin (Sampling.tailCount S))) := by
  classical
  exact Finset.univ.biUnion fun j => supportBadConfigurations (supports j) S K
@[simp] theorem mem_familyBadConfigurations {κ : Type*} [Fintype κ]
    (supports : κ→Finset (Fin n)) (S : Finset (Fin n)) (K : ℕ)
    (p : Equiv.Perm (Fin (Sampling.tailCount S)) × Equiv.Perm (Fin (Sampling.tailCount S))) :
    p∈familyBadConfigurations supports S K ↔ ∃j,p∈supportBadConfigurations (supports j) S K := by
  classical
  simp only [familyBadConfigurations,Finset.mem_biUnion,Finset.mem_univ,true_and]

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

private theorem adjacent_symm {m : ℕ} (Γ : Finset (Fin m)) (a b : Fin m)
    (h : TailAdjacent Γ a b) : TailAdjacent Γ b a := Or.symm h
private theorem sameRun_symm {m : ℕ} (Γ : Finset (Fin m)) (a b : Fin m)
    (h : TailSameRun Γ a b) : TailSameRun Γ b a := by
  change tailInterval b a ⊆ Γ
  rwa [tailInterval_comm]

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

private theorem factor_embedding {m d : ℕ} (f : Fin m ↪ Fin n) (r : Fin d ↪ Fin n)
    (h : ∀i,∃a,f a=r i) : ∃q : Fin d ↪ Fin m,∀i,f (q i)=r i := by
  classical
  let q : Fin d→Fin m := fun i => Classical.choose (h i)
  have he (i : Fin d) : f (q i)=r i := Classical.choose_spec (h i)
  refine ⟨⟨q,?_⟩,he⟩
  intro i j hij
  apply r.injective
  rw [← he i,← he j,hij]
private theorem preimage_of_pair {m : ℕ} (f : Fin m ↪ Fin n) (a b : Fin m)
    (z : Fin n) (hz : z∈({f a,f b} : Finset (Fin n))) : ∃p,f p=z := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  exact hz.elim (fun h => ⟨a,h.symm⟩) (fun h => ⟨b,h.symm⟩)
private theorem pair_positions {m d : ℕ} (f : Fin m ↪ Fin n)
    (r : Fin d ↪ Fin n) (q : Fin d ↪ Fin m) (hq : ∀i,f (q i)=r i)
    (i : Fin d) (a b : Fin m) (h : r i∈({f a,f b} : Finset (Fin n))) :
    q i=a ∨ q i=b := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  exact h.imp (fun he => f.injective ((hq i).trans he))
    (fun he => f.injective ((hq i).trans he))
private theorem tail_selected_ne (S : Finset (Fin n))
    (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (a : Fin (Sampling.tailCount S)) (s : Fin n) (hs : s∈S) :
    Sampling.tail S (τ a)≠s := by
  intro he
  exact Sampling.tail_not_mem S (τ a) (he.symm ▸ hs)

/-- Four original supported tail labels with A geometry are an actual bad-event
witness, for either enumeration of each unordered support pair. -/
theorem caseA_mem_supportBadAt (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (a b c d : Fin (Sampling.tailCount S))
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : Sampling.tail S (τ a)∈T) (hb : Sampling.tail S (τ b)∈T)
    (hc : Sampling.tail S (τ c)∈T) (hd : Sampling.tail S (τ d)∈T)
    (hAdj : TailAdjacent Γ a b) (hRun : TailSameRun Γ c d) :
    τ∈supportBadAt T S Γ := by
  classical
  let f : Fin (Sampling.tailCount S) ↪ Fin n := τ.toEmbedding.trans (Sampling.tail S)
  obtain ⟨R,hR,hO⟩ := exists_acRole T (f a) (f b) (f c) (f d)
    (f.injective.ne hab) (f.injective.ne hac) (f.injective.ne had)
    (f.injective.ne hbc) (f.injective.ne hbd) (f.injective.ne hcd) ha hb hc hd
  have h0 : R.embedding 0∈({f a,f b} : Finset (Fin n)) := by
    rw [ACRole.embedding_zero,← hR]; exact pairEmbedding_mem _ _ 0
  have h1 : R.embedding 1∈({f a,f b} : Finset (Fin n)) := by
    rw [ACRole.embedding_one,← hR]; exact pairEmbedding_mem _ _ 1
  have h2 : R.embedding 2∈({f c,f d} : Finset (Fin n)) := by
    rw [ACRole.embedding_two,← hO]; exact pairEmbedding_mem _ _ 0
  have h3 : R.embedding 3∈({f c,f d} : Finset (Fin n)) := by
    rw [ACRole.embedding_three,← hO]; exact pairEmbedding_mem _ _ 1
  obtain ⟨q,hq⟩ := factor_embedding f R.embedding (by
    intro i; fin_cases i
    · exact preimage_of_pair f a b _ h0
    · exact preimage_of_pair f a b _ h1
    · exact preimage_of_pair f c d _ h2
    · exact preimage_of_pair f c d _ h3)
  apply mem_supportBadAt_of_caseA T S Γ τ R
  apply (mem_caseA T S Γ R τ).mpr
  refine ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,hq⟩
  · exact pair_relation (TailAdjacent Γ) (adjacent_symm Γ) hAdj
      (q.injective.ne (by decide : (0 : Fin 4)≠1))
      (pair_positions f R.embedding q hq 0 a b h0) (pair_positions f R.embedding q hq 1 a b h1)
  · exact pair_relation (TailSameRun Γ) (sameRun_symm Γ) hRun
      (q.injective.ne (by decide : (2 : Fin 4)≠3))
      (pair_positions f R.embedding q hq 2 c d h2) (pair_positions f R.embedding q hq 3 c d h3)

/-- Three original supported tail labels and one supported selected label with
B geometry witness the intrinsic event, retaining the ordered outside roles. -/
theorem caseB_mem_supportBadAt (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (a b z : Fin (Sampling.tailCount S)) (s : Fin n)
    (hab : a≠b) (haz : a≠z) (hbz : b≠z)
    (ha : Sampling.tail S (τ a)∈T) (hb : Sampling.tail S (τ b)∈T)
    (hz : Sampling.tail S (τ z)∈T) (hsT : s∈T) (hsS : s∈S)
    (hAdj : TailAdjacent Γ a b) (hRun : AnchorSameRun Γ z) :
    τ∈supportBadAt T S Γ := by
  classical
  let f : Fin (Sampling.tailCount S) ↪ Fin n := τ.toEmbedding.trans (Sampling.tail S)
  obtain ⟨R,hR,hZ,hS⟩ := exists_bRole T (f a) (f b) (f z) s
    (f.injective.ne hab) (f.injective.ne haz) (tail_selected_ne S τ a s hsS)
    (f.injective.ne hbz) (tail_selected_ne S τ b s hsS)
    (tail_selected_ne S τ z s hsS) ha hb hz hsT
  have h0 : firstThreeLabels R.embedding 0∈({f a,f b} : Finset (Fin n)) := by
    change R.embedding 0∈_; rw [BRole.embedding_zero,← hR]; exact pairEmbedding_mem _ _ 0
  have h1 : firstThreeLabels R.embedding 1∈({f a,f b} : Finset (Fin n)) := by
    change R.embedding 1∈_; rw [BRole.embedding_one,← hR]; exact pairEmbedding_mem _ _ 1
  have h2 : firstThreeLabels R.embedding 2=f z := by
    change R.embedding 2=f z; rw [BRole.embedding_two,hZ]
  obtain ⟨q,hq⟩ := factor_embedding f (firstThreeLabels R.embedding) (by
    intro i; fin_cases i
    · exact preimage_of_pair f a b _ h0
    · exact preimage_of_pair f a b _ h1
    · exact ⟨z,h2.symm⟩)
  apply mem_supportBadAt_of_caseB T S Γ τ R
  apply (mem_caseB T S Γ R τ).mpr
  refine ⟨hS.symm ▸ hsS,q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,hq⟩
  · exact pair_relation (TailAdjacent Γ) (adjacent_symm Γ) hAdj
      (q.injective.ne (by decide : (0 : Fin 3)≠1))
      (pair_positions f _ q hq 0 a b h0) (pair_positions f _ q hq 1 a b h1)
  · have he : q 2=z := f.injective ((hq 2).trans h2)
    rw [he]; exact hRun

/-- Two supported tail labels and two distinct supported selected original
labels with C geometry enter the intrinsic event without ordering either pair. -/
theorem caseC_mem_supportBadAt (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) (τ : Equiv.Perm (Fin (Sampling.tailCount S)))
    (a b : Fin (Sampling.tailCount S)) (s t : Fin n) (hab : a≠b) (hst : s≠t)
    (ha : Sampling.tail S (τ a)∈T) (hb : Sampling.tail S (τ b)∈T)
    (hsT : s∈T) (htT : t∈T) (hsS : s∈S) (htS : t∈S)
    (hAdj : TailAdjacent Γ a b) : τ∈supportBadAt T S Γ := by
  classical
  let f : Fin (Sampling.tailCount S) ↪ Fin n := τ.toEmbedding.trans (Sampling.tail S)
  obtain ⟨R,hR,hO⟩ := exists_acRole T (f a) (f b) s t
    (f.injective.ne hab) (tail_selected_ne S τ a s hsS) (tail_selected_ne S τ a t htS)
    (tail_selected_ne S τ b s hsS) (tail_selected_ne S τ b t htS) hst ha hb hsT htT
  have h0 : firstTwoLabels R.embedding 0∈({f a,f b} : Finset (Fin n)) := by
    change R.embedding 0∈_; rw [ACRole.embedding_zero,← hR]; exact pairEmbedding_mem _ _ 0
  have h1 : firstTwoLabels R.embedding 1∈({f a,f b} : Finset (Fin n)) := by
    change R.embedding 1∈_; rw [ACRole.embedding_one,← hR]; exact pairEmbedding_mem _ _ 1
  obtain ⟨q,hq⟩ := factor_embedding f (firstTwoLabels R.embedding) (by
    intro i; fin_cases i
    · exact preimage_of_pair f a b _ h0
    · exact preimage_of_pair f a b _ h1)
  apply mem_supportBadAt_of_caseC T S Γ τ R
  apply (mem_caseC T S Γ R τ).mpr
  refine ⟨?_,q,(mem_caseCTailPlacements Γ q).mpr ?_,hq⟩
  · rw [hO]
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hsS,htS⟩
  · exact pair_relation (TailAdjacent Γ) (adjacent_symm Γ) hAdj
      (q.injective.ne (by decide : (0 : Fin 2)≠1))
      (pair_positions f _ q hq 0 a b h0) (pair_positions f _ q hq 1 a b h1)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
