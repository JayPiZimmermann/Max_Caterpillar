import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Block
import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Reindex

/-! # Weighted paired baseline attachment in the original physical indexing

An arbitrary selected completion of at least three neurons is connected to a
literal signed baseline pair. The proof starts from its actual all-input
weighted-baseline identity, for every real weight s. The first dictionary and
all unselected physical neurons retain their original coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption
variable {m r k : ℕ}

theorem block_decomposition (a : Network 4 6 (m+r)) (U : Fin 2 → Fin 2 → ℝ)
    (hW : a.W₁=pairedRows U) (hb : a.HasZeroBiases) :
    a=appendSpectators (BaselineFold.completion U
      (fun i=>a.W₂ (Fin.castAdd r i)) 0 (fun i=>a.w₃ (Fin.castAdd r i)) 0)
      (fun i=>a.W₂ (Fin.natAdd m i)) 0 (fun i=>a.w₃ (Fin.natAdd m i)) := by
  apply physical_ext
  · exact hW
  · exact hb.1
  · funext i j
    refine Fin.addCases (fun l=>?_) (fun l=>?_) i
    · simp only [appendSpectators,BaselineFold.completion,Fin.append_left]
    · simp only [appendSpectators,BaselineFold.completion,Fin.append_right]
  · funext i
    rw [hb.2.1]
    refine Fin.addCases (fun l=>?_) (fun l=>?_) i
    · simp only [appendSpectators,BaselineFold.completion,Fin.append_left,Pi.zero_apply]
    · simp only [appendSpectators,BaselineFold.completion,Fin.append_right,Pi.zero_apply]
  · funext i
    refine Fin.addCases (fun l=>?_) (fun l=>?_) i
    · simp only [appendSpectators,BaselineFold.completion,Fin.append_left]
    · simp only [appendSpectators,BaselineFold.completion,Fin.append_right]
  · exact hb.2.2

/-- End-to-end physical weighted baseline connectivity, with no quadrant-fit
premise. All real s, arbitrary invertible paired codes, arbitrary original
second rows, and arbitrary unchanged spectator neurons are included. -/
theorem weighted_baseline_attachment (a : Network 4 6 k) (U : Fin 2 → Fin 2 → ℝ)
    (hW : a.W₁=pairedRows U) (hdet : codeDet U≠0) (hb : a.HasZeroBiases)
    (s : ℝ) (S : Finset (Fin k)) (hS : 3≤S.card)
    (hlocal : ∀ x,(∑ i in S,a.w₃ i*relu (preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x))=
      BaselineWeighted.weightedTarget s x)
    (ha : ∀ x,a.eval x=Maximum 4 x) :
    ∃ p n : Fin k,p∈S ∧ n∈S ∧ p≠n ∧
      JoinedIn (ExactSet 4 6 k) a
        (signedNet a S p n (fun j=>Paired.baselineRow U j+s*comparisonRow U j) 0) := by
  classical
  let e := selectedSecondEquiv S
  let b := reindexSecond a e
  let T := prefixSlots S.card (k-S.card)
  let C := fun i : Fin S.card=>b.W₂ (Fin.castAdd (k-S.card) i)
  let w := fun i : Fin S.card=>b.w₃ (Fin.castAdd (k-S.card) i)
  let rows := fun i : Fin (k-S.card)=>b.W₂ (Fin.natAdd S.card i)
  let sw := fun i : Fin (k-S.card)=>b.w₃ (Fin.natAdd S.card i)
  have hbzero : b.HasZeroBiases := reindexSecond_zeroBiases a e hb
  have hbW : b.W₁=pairedRows U := hW
  have heq : b=appendSpectators (BaselineFold.completion U C 0 w 0) rows 0 sw :=
    block_decomposition b U hbW hbzero
  have hbexact : ∀ x,b.eval x=Maximum 4 x := fun x=>(reindexSecond_eval a e x).trans (ha x)
  have hfit : ∀ x,(BaselineFold.completion U C 0 w 0).eval x=BaselineWeighted.weightedTarget s x := by
    intro x
    change (∑ i : Fin S.card,w i*relu (preact (pairedRows U) 0 (C i) 0 x))+0=_
    rw [add_zero]
    have hterm (i : Fin S.card) : w i*relu (preact (pairedRows U) 0 (C i) 0 x)=
        a.w₃ (e (Fin.castAdd (k-S.card) i))*relu
          (preact a.W₁ a.b₁ (a.W₂ (e (Fin.castAdd (k-S.card) i)))
            (a.b₂ (e (Fin.castAdd (k-S.card) i))) x) := by
      change a.w₃ (e (Fin.castAdd (k-S.card) i))*relu
        (preact (pairedRows U) 0 (a.W₂ (e (Fin.castAdd (k-S.card) i))) 0 x)=_
      rw [hW,hb.1,hb.2.1]
      rfl
    simp_rw [hterm]
    exact (sum_selected_prefix S (fun i=>a.w₃ i*relu
      (preact a.W₁ a.b₁ (a.W₂ i) (a.b₂ i) x))).trans (hlocal x)
  have hsource : ∀ x,(appendSpectators (BaselineFold.completion U C 0 w 0) rows 0 sw).eval x=
      Maximum 4 x := by
    intro x
    rw [← heq]
    exact hbexact x
  obtain ⟨p,n,hp,hn,hpn,hj⟩ := weighted_baseline_block_attachment U hdet s hS C w hfit rows 0 sw hsource
  have hblock : JoinedIn (ExactSet 4 6 (S.card+(k-S.card))) b
      (signedNet b T p n (baselineRow U s) 0) := by
    simpa only [← heq] using hj
  have hback := joinedIn_reindexSecond_mapBack a (signedNet b T p n (baselineRow U s) 0) e hblock
  have hT : ∀ i,i∈T ↔ e i∈S := selected_prefix_iff S
  have htarget := reindex_signedNet_mapBack a e S T hT p n (baselineRow U s) 0
  have hpS : e p∈S := (hT p).mp hp
  have hnS : e n∈S := (hT n).mp hn
  refine ⟨e p,e n,hpS,hnS,fun h=>hpn (e.injective h),?_⟩
  change JoinedIn (ExactSet 4 6 k) a
    (reindexSecond (signedNet (reindexSecond a e) T p n (baselineRow U s) 0) e.symm) at hback
  rw [htarget] at hback
  simpa only [baselineRow_eq_comparator] using hback

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
