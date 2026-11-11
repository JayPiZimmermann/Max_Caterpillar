import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Clear

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption QuadrantGroups
variable {N m k : ℕ} [NeZero N]

theorem signedAttached_literal (a : Network N m k) (S : Finset (Fin k))
    (Q R : Fin m → ℝ) (q r : ℝ) (h : SignedBaselineAttached a S Q R q r) :
    ∃ p n : Fin k,p∈S ∧ n∈S ∧ p≠n ∧
      JoinedIn (ExactSet N m k) a (signedNet a S p n (fun j=>Q j-R j) (q-r)) := by
  rcases h with ⟨mid,p,n,hp,hn,hpn,hA,hβ,hθ,hdp,hdn,hspec,hj⟩
  let b := withSecondRows mid (signedChordRows mid S p n (fun j=>Q j-R j))
    (signedChordBiases mid S p n (q-r))
  have hpair := signedChord_endpoint_pair mid S p n (fun j=>Q j-R j) (q-r) hpn
  have hc := clear_signed_joinedIn b hj.target_mem S p n hpn (fun j=>Q j-R j) (q-r)
    ⟨hpair.1,hpair.2.1,hdp⟩ ⟨hpair.2.2.1,hpair.2.2.2,hdn⟩
    (fun i hi hip hin => signedChord_endpoint_unused mid S p n i (fun j=>Q j-R j) (q-r) hi hip hin)
  have hagree : AgreeOutside a b S := by
    refine ⟨hA,hβ,hθ,?_⟩
    intro i hi
    have hip : i≠p := by rintro rfl; exact hi hp
    have hin : i≠n := by rintro rfl; exact hi hn
    simpa only [b,withSecondRows,signedChordRows,signedChordBiases,
      if_neg hip,if_neg hin,if_neg hi] using hspec i hi
  have heq := signedNet_congr_source a b S p n (fun j=>Q j-R j) (q-r) hagree
  exact ⟨p,n,hp,hn,hpn,by simpa only [heq] using hj.trans hc⟩

theorem splitAttached_literal (a : Network N m k) (S : Finset (Fin k))
    (Q R : Fin m → ℝ) (q r : ℝ) (α β : Fin k → ℝ)
    (h : SplitBaselineAttached a S Q R q r α β) :
    ∃ p n : Fin k,p∈S ∧ n∈S ∧ p≠n ∧
      JoinedIn (ExactSet N m k) a (splitNet a S p n Q R q r) := by
  let mid := eraseCrossingNet a S α β
  rcases h with ⟨p,n,hp,hn,hpn,hdp,hdn,hj⟩
  let b := withSecondRows mid (splitTargetRows mid Q R S p n) (splitTargetBiases mid q r S p n)
  let c := PairNormalization.normalizePair b p n
  have hbpos : 0<b.w₃ p := hdp
  have hbneg : b.w₃ n<0 := hdn
  have hnorm : JoinedIn (ExactSet N m k) b c :=
    PairNormalization.normalizePair_joinedIn_exact ⟨b,hj.target_mem⟩ p n hbpos hbneg
  have hcp : c.W₂ p=Q ∧ c.b₂ p=q ∧ c.w₃ p=1 := by
    refine ⟨?_,?_,PairNormalization.normalizePair_output_pos b p n hbpos⟩
    · funext j
      simp only [c,PairNormalization.normalizePair,scaleSecond,PairNormalization.pairScales,
        b,withSecondRows,splitTargetRows,if_pos rfl,if_true]
      field_simp [ne_of_gt hdp]
      ring
    · simp only [c,PairNormalization.normalizePair,scaleSecond,PairNormalization.pairScales,
        b,withSecondRows,splitTargetBiases,if_pos rfl,if_true]
      field_simp [ne_of_gt hdp]
      ring
  have hcn : c.W₂ n=R ∧ c.b₂ n=r ∧ c.w₃ n= -1 := by
    refine ⟨?_,?_,PairNormalization.normalizePair_output_neg b p n hpn hbneg⟩
    · funext j
      simp only [c,PairNormalization.normalizePair,scaleSecond,PairNormalization.pairScales,
        b,withSecondRows,splitTargetRows,if_neg (Ne.symm hpn),if_pos rfl,if_true]
      field_simp [ne_of_lt hdn]
      ring
    · simp only [c,PairNormalization.normalizePair,scaleSecond,PairNormalization.pairScales,
        b,withSecondRows,splitTargetBiases,if_neg (Ne.symm hpn),if_pos rfl,if_true]
      field_simp [ne_of_lt hdn]
      ring
  have hzero : ∀ i∈S,i≠p → i≠n → c.W₂ i=0 ∧ c.b₂ i=0 := by
    intro i hi hip hin
    rcases PairNormalization.normalizePair_unselected b p n i hip hin with ⟨hwi,hbi,_⟩
    constructor
    · rw [hwi]
      funext j
      simp only [b,withSecondRows,splitTargetRows,if_neg hip,if_neg hin,if_pos hi,Pi.zero_apply]
    · rw [hbi]
      simp only [b,withSecondRows,splitTargetBiases,if_neg hip,if_neg hin,if_pos hi]
  have hclear := clear_split_joinedIn c hnorm.target_mem S p n hpn Q R q r hcp hcn hzero
  have hb_agree : AgreeOutside a b S := by
    refine ⟨rfl,rfl,rfl,?_⟩
    intro i hi
    have hip : i≠p := by rintro rfl; exact hi hp
    have hin : i≠n := by rintro rfl; exact hi hn
    refine ⟨?_,?_,?_⟩
    · funext j
      simp only [b,mid,withSecondRows,splitTargetRows,if_neg hip,if_neg hin,if_neg hi,
        eraseCrossingNet,withOutput]
    · simp only [b,mid,withSecondRows,splitTargetBiases,if_neg hip,if_neg hin,if_neg hi,
        eraseCrossingNet,withOutput]
    · simp [b,mid,withSecondRows,eraseCrossingNet,withOutput,eraseClusterOutput,hi]
  have hc_agree : AgreeOutside a c S := by
    refine ⟨rfl,rfl,rfl,?_⟩
    intro i hi
    have hip : i≠p := by rintro rfl; exact hi hp
    have hin : i≠n := by rintro rfl; exact hi hn
    rcases PairNormalization.normalizePair_unselected b p n i hip hin with ⟨hw,hb,hd⟩
    exact ⟨hw.trans (hb_agree.2.2.2 i hi).1,hb.trans (hb_agree.2.2.2 i hi).2.1,
      hd.trans (hb_agree.2.2.2 i hi).2.2⟩
  have heq := splitNet_congr_source a c S p n Q R q r hc_agree
  exact ⟨p,n,hp,hn,hpn,by simpa only [heq] using (hj.trans hnorm).trans hclear⟩

theorem quadrant_literal_alternative (a : Network N m k) (S : Finset (Fin k))
    (Q R : Fin m → ℝ) (q r : ℝ) (α β : Fin k → ℝ)
    (hrow : ∀ i∈S,∀ j,a.W₂ i j=α i*Q j+β i*R j)
    (hbias : ∀ i∈S,a.b₂ i=α i*q+β i*r)
    (hQ : ∀ x,0≤preact a.W₁ a.b₁ Q q x) (hR : ∀ x,0≤preact a.W₁ a.b₁ R r x)
    (hfit : ∀ u v : ℝ,0≤u → 0≤v → (∑ i in S,a.w₃ i*max 0 (α i*u+β i*v))=u-v)
    (ha : ∀ x,a.eval x=Maximum N x) :
    (∃ p n : Fin k,p∈S ∧ n∈S ∧ p≠n ∧
      JoinedIn (ExactSet N m k) a (signedNet a S p n (fun j=>Q j-R j) (q-r))) ∨
    (∃ p n : Fin k,p∈S ∧ n∈S ∧ p≠n ∧
      JoinedIn (ExactSet N m k) a (splitNet a S p n Q R q r)) := by
  rcases quadrant_baseline_attachment a S Q R q r α β hrow hbias hQ hR hfit ha with hs|hs
  · exact Or.inl (signedAttached_literal a S Q R q r hs)
  · exact Or.inr (splitAttached_literal a S Q R q r α β hs)

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
