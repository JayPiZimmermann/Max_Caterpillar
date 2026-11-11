import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Compression.Grouped

/-! # Actual common-support four-slot compression and attachment

The four comparison rows are partitioned by support membership and physical
orientation. All four output groups merge simultaneously; empty groups reuse
dormant rows. The resulting rows are an actual hidden permutation of the
carrier/pair/comparator representative.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m : ℕ}

noncomputable def commonSupportGroup (S : Finset (Fin 4)) (flip : Fin 4 → Bool)
    (i : Fin 4) : Fin 4 :=
  if i∈S then (if flip i then 1 else 0) else (if flip i then 3 else 2)

noncomputable def commonSupportRows (D H : Fin m → ℝ) : Fin 4 → Fin m → ℝ :=
  ![D-H,-(D-H),D,-D]

lemma commonSupport_row (S : Finset (Fin 4)) (flip : Fin 4 → Bool)
    (D H : Fin m → ℝ) (i : Fin 4) :
    commonSupportRows D H (commonSupportGroup S flip i)=
      if flip i then -(D-(if i∈S then H else 0)) else D-(if i∈S then H else 0) := by
  classical
  by_cases hi : i∈S <;> cases hf : flip i <;>
    norm_num [commonSupportRows,commonSupportGroup,hi,hf] <;> rfl

lemma commonSupport_net (A : Fin m → Point N) (β B D H : Fin m → ℝ)
    (j : Fin 4 → ℝ) (flip : Fin 4 → Bool) (S : Finset (Fin 4)) :
    orientedCompletionNet A β B D (fun i => if i∈S then H else 0) j flip=
      fourGroupedNet A β (carrierRow j flip B D (fun i => if i∈S then H else 0))
        (commonSupportRows D H) j (commonSupportGroup S flip) := by
  unfold orientedCompletionNet fourGroupedNet
  congr 1
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  exact (commonSupport_row S flip D H i).symm

/-- Extend a local-slot permutation by the fixed carrier slot. -/
def liftLocalPerm (e : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 5) :=
  (finSuccEquiv 4).trans ((Equiv.optionCongr e).trans (finSuccEquiv 4).symm)

@[simp] lemma liftLocalPerm_zero (e : Equiv.Perm (Fin 4)) : liftLocalPerm e 0=0 := by
  simp [liftLocalPerm]

@[simp] lemma liftLocalPerm_succ (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    liftLocalPerm e i.succ=(e i).succ := by
  simp [liftLocalPerm]

noncomputable def fourCanonicalNet (A : Fin m → Point N) (β g : Fin m → ℝ)
    (R : Fin 4 → Fin m → ℝ) (w : Fin 4 → ℝ) : Network N m 5 where
  W₁ := A
  b₁ := β
  W₂ := Fin.cons g R
  b₂ := 0
  w₃ := Fin.cons 1 w
  b₃ := 0

lemma fourGroupedTarget_permutation (A : Fin m → Point N) (β g : Fin m → ℝ)
    (R : Fin 4 → Fin m → ℝ) (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4)
    (e : Equiv.Perm (Fin 4)) :
    fourGroupedTarget A β g R j group e=
      permuteHidden (fourCanonicalNet A β g R (groupTotal j group))
        (Equiv.refl _) (liftLocalPerm e.symm) := by
  unfold fourGroupedTarget permuteHidden fourCanonicalNet
  congr 1
  · funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  · funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp

lemma commonSupport_total_support (j : Fin 4 → ℝ) (flip : Fin 4 → Bool)
    (S : Finset (Fin 4)) :
    groupTotal j (commonSupportGroup S flip) 0+
      groupTotal j (commonSupportGroup S flip) 1=∑ i in S,j i := by
  classical
  calc
    _ = ∑ i,if i∈S then j i else 0 := by
      rw [groupTotal,groupTotal,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈S <;> cases hf : flip i <;>
        simp [commonSupportGroup,hi,hf,show (2:Fin 4)≠0 from by decide,
          show (2:Fin 4)≠1 from by decide,show (3:Fin 4)≠0 from by decide,
          show (3:Fin 4)≠1 from by decide]
    _ = _ := by
      simp

lemma groupTotal_total (j : Fin 4 → ℝ) (group : Fin 4 → Fin 4) :
    (∑ a,groupTotal j group a)=∑ i,j i := by
  have h := groupTotal_sum j (fun _ => 1) group
  simpa only [mul_one] using h

lemma commonSupport_canonical (A : Fin m → Point N) (β g D H : Fin m → ℝ)
    (j : Fin 4 → ℝ) (flip : Fin 4 → Bool) (S : Finset (Fin 4))
    (hS : ∑ i in S,j i=0) (hj : ∑ i,j i=1) :
    fourCanonicalNet A β g (commonSupportRows D H) (groupTotal j (commonSupportGroup S flip))=
      carrierPairNet A β g (D-H) D 0 0 0 0 1
        (groupTotal j (commonSupportGroup S flip) 0)
        (groupTotal j (commonSupportGroup S flip) 3) := by
  have h01 := commonSupport_total_support j flip S
  rw [hS] at h01
  have hall := groupTotal_total j (commonSupportGroup S flip)
  rw [hj] at hall
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hall
  change groupTotal j (commonSupportGroup S flip) 0+
    (groupTotal j (commonSupportGroup S flip) 1+
      (groupTotal j (commonSupportGroup S flip) 2+groupTotal j (commonSupportGroup S flip) 3))=1 at hall
  have h1 : groupTotal j (commonSupportGroup S flip) 1=
      -groupTotal j (commonSupportGroup S flip) 0 := by linarith only [h01]
  have h2 : groupTotal j (commonSupportGroup S flip) 2=
      1-groupTotal j (commonSupportGroup S flip) 3 := by linarith only [hall,h01]
  have hw : Fin.cons 1 (groupTotal j (commonSupportGroup S flip))=
      ![1,groupTotal j (commonSupportGroup S flip) 0,
        -groupTotal j (commonSupportGroup S flip) 0,
        1-groupTotal j (commonSupportGroup S flip) 3,
        groupTotal j (commonSupportGroup S flip) 3] := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    simp only [Fin.cons_succ]
    fin_cases i
    · rfl
    · exact h1
    · exact h2
    · rfl
  unfold fourCanonicalNet carrierPairNet
  congr 1
  all_goals first | exact hw | (funext i; fin_cases i <;> simp)

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment

namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {N m : ℕ}

/-- A genuine hidden permutation transports an actual exact-parameter path. -/
theorem joinedIn_permuteHidden [NeZero N] {a b : Network N m 5}
    (h : JoinedIn (ExactSet N m 5) a b) (q : Equiv.Perm (Fin 5)) :
    JoinedIn (ExactSet N m 5) (permuteHidden a (Equiv.refl _) q)
      (permuteHidden b (Equiv.refl _) q) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p.map (continuous_permuteHidden (Equiv.refl _) q),?_⟩
  intro t x
  change (permuteHidden (p t) (Equiv.refl _) q).eval x=Maximum N x
  rw [permuteHidden_eval]
  exact hp t x

/-- Four common-support comparison slots reach the actual three-slot
carrier-pair endpoint. All intermediate points are physical five-slot
parameters in the exact fiber. The finite support may have any size. -/
theorem commonSupport_attaches [NeZero N]
    (A : Fin m → Point N) (β B D H : Fin m → ℝ)
    (j : Fin 4 → ℝ) (flip : Fin 4 → Bool) (S : Finset (Fin 4))
    (hS : ∑ i in S,j i=0) (hj : ∑ i,j i=1)
    (hg : ∀ x,0≤preact A β (carrierRow j flip B D (fun i => if i∈S then H else 0)) 0 x)
    (hexact : ∀ x,(orientedCompletionNet A β B D (fun i => if i∈S then H else 0) j flip).eval x=Maximum N x)
    (hmax : ∀ x,preact A β B 0 x+relu (preact A β D 0 x)=Maximum N x)
    (x₀ : Point N) (hD : preact A β D 0 x₀=0) (hB : preact A β B 0 x₀<0) :
    ∃ e : Equiv.Perm (Fin 4),
      JoinedIn (ExactSet N m 5)
        (orientedCompletionNet A β B D (fun i => if i∈S then H else 0) j flip)
        (permuteHidden
          (carrierPairChord A β
            (carrierRow j flip B D (fun i => if i∈S then H else 0)) (D-H) D B
            0 0 0 0 0 1 (groupTotal j (commonSupportGroup S flip) 0)
            (groupTotal j (commonSupportGroup S flip) 3) 1)
          (Equiv.refl _) (liftLocalPerm e.symm)) := by
  let g := carrierRow j flip B D (fun i => if i∈S then H else 0)
  let group := commonSupportGroup S flip
  let K := groupTotal j group 0
  let s := groupTotal j group 3
  have hs := commonSupport_net A β B D H j flip S
  have hex : ∀ x,(fourGroupedNet A β g (commonSupportRows D H) j group).eval x=Maximum N x := by
    intro x
    rw [← hs]
    exact hexact x
  obtain ⟨e,he⟩ := fourGrouped_compress A β g (commonSupportRows D H) j group hex
  have htarget : fourGroupedTarget A β g (commonSupportRows D H) j group e=
      permuteHidden (carrierPairNet A β g (D-H) D 0 0 0 0 1 K s)
        (Equiv.refl _) (liftLocalPerm e.symm) := by
    rw [fourGroupedTarget_permutation,commonSupport_canonical A β g D H j flip S hS hj]
  have hcExact : ∀ x,(carrierPairNet A β g (D-H) D 0 0 0 0 1 K s).eval x=Maximum N x := by
    intro x
    have hh := he.target_mem x
    rw [htarget,permuteHidden_eval] at hh
    exact hh
  have hc := carrierPair_attaches A β g (D-H) D B 0 0 0 0 0 1 K s
    (by norm_num) hg hcExact (fun x => by simpa only [add_zero] using (hmax x).symm)
    x₀ hD hB
  refine ⟨e,?_⟩
  rw [hs]
  apply he.trans
  rw [htarget]
  exact joinedIn_permuteHidden hc (liftLocalPerm e.symm)

/-- Relabeling the constructed endpoint preserves its three-slot support. -/
theorem permuted_carrierPairChord_one_support
    (A : Fin m → Point N) (β : Fin m → ℝ) (g H D B : Fin m → ℝ)
    (γ η δ ζ θ d K s : ℝ) (q : Equiv.Perm (Fin 5)) :
    ∃ T : Finset (Fin 5),T.card≤3 ∧ ∀ i,i∉T →
      (permuteHidden (carrierPairChord A β g H D B γ η δ ζ θ d K s 1)
        (Equiv.refl _) q).w₃ i=0 ∨
      ((permuteHidden (carrierPairChord A β g H D B γ η δ ζ θ d K s 1)
        (Equiv.refl _) q).W₂ i=0 ∧
       (permuteHidden (carrierPairChord A β g H D B γ η δ ζ θ d K s 1)
        (Equiv.refl _) q).b₂ i=0) := by
  classical
  refine ⟨({1,2,3} : Finset (Fin 5)).image q.symm,?_,?_⟩
  · exact (Finset.card_image_le).trans (by decide)
  · intro i hi
    have hn : q i∉({1,2,3} : Finset (Fin 5)) := by
      intro h
      apply hi
      exact Finset.mem_image.mpr ⟨q i,h,q.symm_apply_apply i⟩
    exact carrierPairChord_one_support A β g H D B γ η δ ζ θ d K s (q i) hn

/-- The constructed actual endpoint has at most three contributing slots. -/
theorem commonSupport_attaches_threeSlots {N m : ℕ} [NeZero N]
    (A : Fin m → Point N) (β B D H : Fin m → ℝ)
    (j : Fin 4 → ℝ) (flip : Fin 4 → Bool) (S : Finset (Fin 4))
    (hS : ∑ i in S,j i=0) (hj : ∑ i,j i=1)
    (hg : ∀ x,0≤preact A β (carrierRow j flip B D (fun i => if i∈S then H else 0)) 0 x)
    (hexact : ∀ x,(orientedCompletionNet A β B D (fun i => if i∈S then H else 0) j flip).eval x=Maximum N x)
    (hmax : ∀ x,preact A β B 0 x+relu (preact A β D 0 x)=Maximum N x)
    (x₀ : Point N) (hD : preact A β D 0 x₀=0) (hB : preact A β B 0 x₀<0) :
    ∃ net : Network N m 5,
      JoinedIn (ExactSet N m 5)
        (orientedCompletionNet A β B D (fun i => if i∈S then H else 0) j flip) net ∧
      ∃ T : Finset (Fin 5),T.card≤3 ∧ ∀ i,i∉T →
        net.w₃ i=0 ∨ (net.W₂ i=0 ∧ net.b₂ i=0) := by
  obtain ⟨e,he⟩ := commonSupport_attaches A β B D H j flip S hS hj hg hexact hmax x₀ hD hB
  exact ⟨_,he,permuted_carrierPairChord_one_support A β _ (D-H) D B
    0 0 0 0 0 1 _ _ (liftLocalPerm e.symm)⟩


end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
