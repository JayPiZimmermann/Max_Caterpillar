import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.Two
import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups.ClusterPath

/-! At most two target comparisons attach without activation-pattern assumptions. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
open BigOperators Absorption QuadrantGroups

theorem target_cluster_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (C : Finset (Fin 5)) (hcard : C.card ≤ 2) (flip : Fin 5 → Bool)
    (hsum : (∑ i in C,a.val.w₃ i)=1)
    (hnatural : ∀ i∈C, ∀ x, endpointForm U (a.val.W₂ i) x =
      if flip i then -endpointForm U (comparisonRow U) x else endpointForm U (comparisonRow U) x) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  classical
  have hC : C.Nonempty := by
    by_contra hh
    have he : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    simp [he] at hsum
  obtain ⟨c,hc⟩ := hC
  by_cases hsame : ∀ i∈C,flip i=flip c
  · have hpreact (i : Fin 5) (x : Point 4) :
        preact a.val.W₁ a.val.b₁ (a.val.W₂ i) (a.val.b₂ i) x =
          endpointForm U (a.val.W₂ i) x := by
      rw [hU,hb.1,hb.2.1]
      exact preact_pairedRows_zero U _ x
    have hpre : ∀ i∈C,∀ x,preact a.val.W₁ a.val.b₁ (a.val.W₂ i) (a.val.b₂ i) x=
        (1:ℝ)*preact a.val.W₁ a.val.b₁ (a.val.W₂ c) (a.val.b₂ c) x := by
      intro i hi x
      rw [hpreact,hpreact,one_mul,hnatural i hi x,hnatural c hc x,hsame i hi]
    have hj := mergeCluster_joinedIn_exact a C c (fun _ => 1) (by intros; norm_num) hpre
    let b : ExactFiber 4 6 5 :=
      ⟨withOutput a.val (mergeClusterOutput a.val.w₃ C c (fun _ => 1)) a.val.b₃,hj.target_mem⟩
    have hbc : b.val.w₃ c=1 := by
      change mergeClusterOutput a.val.w₃ C c (fun _ => 1) c=1
      rw [mergeClusterOutput_rep _ _ _ _ hc]
      simpa only [mul_one] using hsum
    have hbb : b.val.HasZeroBiases := hb
    have hunit := unit_comparison_quotient_joined b U hdet hU hbb c (flip c) hbc
      (hnatural c hc)
    exact (quotient_joined_of_joinedIn a b hj).trans hunit
  · push_neg at hsame
    obtain ⟨n,hn,hneq⟩ := hsame
    have hroles : ∃ cp cn : Fin 5,cp∈C ∧ cn∈C ∧ flip cp=false ∧ flip cn=true := by
      cases hfc : flip c <;> cases hfn : flip n
      · simp_all
      · exact ⟨c,n,hc,hn,hfc,hfn⟩
      · exact ⟨n,c,hn,hc,hfn,hfc⟩
      · simp_all
    obtain ⟨cp,cn,hcp,hcn,hfp,hfn⟩ := hroles
    have hpn : cp≠cn := by
      intro hh
      have hf := congrArg flip hh
      rw [hfp,hfn] at hf
      contradiction
    have hsub : ({cp,cn} : Finset (Fin 5)) ⊆ C := by
      intro i hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · simpa only [hi] using hcp
      · simpa only [Finset.mem_singleton.mp hi] using hcn
    have heq : ({cp,cn} : Finset (Fin 5))=C :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hpn] using hcard)
    have hw : a.val.w₃ cp+a.val.w₃ cn=1 := by
      simpa [← heq,hpn] using hsum
    apply two_comparisons_quotient_joined a U hdet hU hb cp cn hpn hw
    · intro x
      simpa [hfp] using hnatural cp hcp x
    · intro x
      simpa [hfn] using hnatural cn hcn x

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
