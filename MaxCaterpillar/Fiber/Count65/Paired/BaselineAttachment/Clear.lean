import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Basic

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption QuadrantGroups
variable {N m k : ℕ} [NeZero N]

theorem clear_pair_readout_joinedIn (a : Network N m k) (ha : ∀ x,a.eval x=Maximum N x)
    (S : Finset (Fin k)) (p n : Fin k) (hpn : p≠n)
    (hdp : a.w₃ p=1) (hdn : a.w₃ n= -1)
    (hzero : ∀ i∈S,i≠p → i≠n → a.W₂ i=0 ∧ a.b₂ i=0) :
    JoinedIn (ExactSet N m k) a (withOutput a (readout a S p n) a.b₃) := by
  let D := (S.erase p).erase n
  have hrows : ∀ i∈D,a.W₂ i=0 := by
    intro i hi
    rcases Finset.mem_erase.mp hi with ⟨hin,hi⟩
    rcases Finset.mem_erase.mp hi with ⟨hip,hi⟩
    exact (hzero i hi hip hin).1
  have hbias : ∀ i∈D,a.b₂ i=0 := by
    intro i hi
    rcases Finset.mem_erase.mp hi with ⟨hin,hi⟩
    rcases Finset.mem_erase.mp hi with ⟨hip,hi⟩
    exact (hzero i hi hip hin).2
  have hout : eraseClusterOutput a.w₃ D=readout a S p n := by
    funext i
    by_cases hip : i=p
    · subst i
      simp [eraseClusterOutput,D,readout,hdp]
    · by_cases hin : i=n
      · subst i
        simp [eraseClusterOutput,D,readout,hdn,Ne.symm hpn]
      · by_cases hi : i∈S <;>
          simp [eraseClusterOutput,D,readout,hip,hin,hi]
  simpa only [hout] using clearZeroRows_joinedIn a ha D hrows hbias

theorem clear_signed_joinedIn (a : Network N m k) (ha : ∀ x,a.eval x=Maximum N x)
    (S : Finset (Fin k)) (p n : Fin k) (hpn : p≠n)
    (L : Fin m → ℝ) (η : ℝ)
    (hp : a.W₂ p=L ∧ a.b₂ p=η ∧ a.w₃ p=1)
    (hn : a.W₂ n= -L ∧ a.b₂ n= -η ∧ a.w₃ n= -1)
    (hzero : ∀ i∈S,i≠p → i≠n → a.W₂ i=0 ∧ a.b₂ i=0) :
    JoinedIn (ExactSet N m k) a (signedNet a S p n L η) := by
  have hj := clear_pair_readout_joinedIn a ha S p n hpn hp.2.2 hn.2.2 hzero
  have heq : withOutput a (readout a S p n) a.b₃=signedNet a S p n L η := by
    apply physical_ext
    · rfl
    · rfl
    · funext i
      by_cases hip : i=p
      · subst i; simpa only [withOutput,signedNet,signedChordRows,if_pos rfl,if_true] using hp.1
      · by_cases hin : i=n
        · subst i
          simpa only [withOutput,signedNet,signedChordRows,if_neg (Ne.symm hpn),if_pos rfl,if_true] using hn.1
        · by_cases hi : i∈S
          · simpa only [withOutput,signedNet,signedChordRows,if_neg hip,if_neg hin,if_pos hi]
              using (hzero i hi hip hin).1
          · simp only [withOutput,signedNet,signedChordRows,if_neg hip,if_neg hin,if_neg hi]
    · funext i
      by_cases hip : i=p
      · subst i; simpa only [withOutput,signedNet,signedChordBiases,if_pos rfl,if_true] using hp.2.1
      · by_cases hin : i=n
        · subst i
          simpa only [withOutput,signedNet,signedChordBiases,if_neg (Ne.symm hpn),if_pos rfl,if_true] using hn.2.1
        · by_cases hi : i∈S
          · simpa only [withOutput,signedNet,signedChordBiases,if_neg hip,if_neg hin,if_pos hi]
              using (hzero i hi hip hin).2
          · simp only [withOutput,signedNet,signedChordBiases,if_neg hip,if_neg hin,if_neg hi]
    · rfl
    · rfl
  simpa only [heq] using hj

theorem clear_split_joinedIn (a : Network N m k) (ha : ∀ x,a.eval x=Maximum N x)
    (S : Finset (Fin k)) (p n : Fin k) (hpn : p≠n)
    (Q R : Fin m → ℝ) (q r : ℝ)
    (hp : a.W₂ p=Q ∧ a.b₂ p=q ∧ a.w₃ p=1)
    (hn : a.W₂ n=R ∧ a.b₂ n=r ∧ a.w₃ n= -1)
    (hzero : ∀ i∈S,i≠p → i≠n → a.W₂ i=0 ∧ a.b₂ i=0) :
    JoinedIn (ExactSet N m k) a (splitNet a S p n Q R q r) := by
  have hj := clear_pair_readout_joinedIn a ha S p n hpn hp.2.2 hn.2.2 hzero
  have heq : withOutput a (readout a S p n) a.b₃=splitNet a S p n Q R q r := by
    apply physical_ext
    · rfl
    · rfl
    · funext i
      by_cases hip : i=p
      · subst i; simpa only [withOutput,splitNet,if_pos rfl,if_true] using hp.1
      · by_cases hin : i=n
        · subst i
          simpa only [withOutput,splitNet,if_neg (Ne.symm hpn),if_pos rfl,if_true] using hn.1
        · by_cases hi : i∈S
          · simpa only [withOutput,splitNet,if_neg hip,if_neg hin,if_pos hi] using (hzero i hi hip hin).1
          · simp only [withOutput,splitNet,if_neg hip,if_neg hin,if_neg hi]
    · funext i
      by_cases hip : i=p
      · subst i; simpa only [withOutput,splitNet,if_pos rfl,if_true] using hp.2.1
      · by_cases hin : i=n
        · subst i
          simpa only [withOutput,splitNet,if_neg (Ne.symm hpn),if_pos rfl,if_true] using hn.2.1
        · by_cases hi : i∈S
          · simpa only [withOutput,splitNet,if_neg hip,if_neg hin,if_pos hi] using (hzero i hi hip hin).2
          · simp only [withOutput,splitNet,if_neg hip,if_neg hin,if_neg hi]
    · rfl
    · rfl
  simpa only [heq] using hj

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
